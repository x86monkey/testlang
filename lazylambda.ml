open Llvm
open Core
open Sexplib
open Sexplib.Conv
open Ctypes
open Foreign

type unmarked
type marked

type _ ast =
  | Num : int -> _ ast 
  | Var : string -> _ ast
  | Lambda : string * unmarked ast -> unmarked ast
  | App : 't ast * 't ast -> 't ast

type val_place = Arg | Scope of int
type getter = { place: val_place; f: llvalue }
(* variable can be arg of current lambda or been captured in closure, int shows pos in scope *)

type context = { unbound: string list;
                 (* unbound variables needed to compile closure *)
                 compile: getter list -> llbuilder -> llvalue 
                 (*          getters      local bldr   code *) }

let undefined () = failwith "undefined"

let llc = global_context ()
let llm = create_module llc "ololo"

let i8_t = i8_type llc
let i8_ptr = pointer_type i8_t
let const_i8_t = const_int i8_t
let i64_t = i64_type llc
let i64_ptr = pointer_type i64_t
let const_i64_t = const_int i64_t
let i32_t = i32_type llc
let i32_ptr = pointer_type i32_t
let const_i32_t = const_int i32_t
let zero = const_i32_t 0

let tag_t = i32_t
let tag = const_int tag_t
let tag_ref x llb = build_gep x [| zero; zero |] "" llb

let unified_t = named_struct_type llc ""
let unified_ptr = pointer_type unified_t
let unified_ptr_ptr = pointer_type unified_ptr

let scope_t = pointer_type unified_ptr
let scope_ptr = pointer_type scope_t
let fun_t  = function_type unified_ptr [| unified_ptr; scope_t |]
let fun_ptr = pointer_type fun_t
let fun_ptr_ptr = pointer_type fun_ptr

let num_t = struct_type llc [| tag_t; i64_t |]
let num_tag = tag 0
let num_ptr = pointer_type num_t
let num_ref x llb = build_gep x [| zero; const_i32_t 1 |] "" llb

let lambda_t = struct_type llc [| tag_t; fun_ptr; scope_t |]
let lambda_tag = tag 1
let lambda_ptr = pointer_type lambda_t
let fun_ref x llb  =  build_bitcast (build_gep x [| zero; const_i32_t 1 |] "" llb) fun_ptr_ptr "" llb
let scope_ref x llb = build_bitcast (build_gep x [| zero; const_i32_t 2 |] "" llb) scope_ptr "" llb
let app_t = struct_type llc [| tag_t; unified_ptr; lambda_ptr |]
let app_tag = tag 2
let app_ptr = pointer_type app_t
let arg_ref x llb = build_bitcast (build_gep x [| zero; const_i32_t 1 |] "" llb) unified_ptr_ptr "" llb
let lambda_ref x llb = build_bitcast (build_gep x [| zero; const_i32_t 2 |] "" llb) unified_ptr_ptr "" llb

let build_new t llb = let raw = build_malloc t "" llb in
                                       build_bitcast raw (pointer_type t) "" llb

let return v llb = build_bitcast v unified_ptr "" llb

let rec join l1 l2 = match l1 with
  | [] -> l2
  | (hd::tl) -> if List.exists l2 (fun el -> el = hd) then join tl l2 else
                 join tl (hd::l2)

let index_list l = let rec iter = function
                     | _, [] -> []
                     | x, hd::tl -> (hd, x)::iter (x + 1, tl) in
                   iter (0, l)

let collect_args names values necessary =
  let indexed = index_list names in
  let rec iter = function
    | [] -> []
    | hd::tl -> let index = List.Assoc.find_exn indexed ~equal:(=) hd in
                List.nth_exn values index :: iter tl
  in iter necessary

let rec exclude elt = function
  | [] -> []
  | hd::tl -> let l = exclude elt tl in
              if hd = elt then l else hd::l

let unify x llb = build_bitcast x unified_ptr "" llb

let build_num x llb = let pnum = build_new num_t llb in
                      let _ = build_store num_tag (tag_ref pnum llb) llb in
                      let _ = build_store x (num_ref pnum llb) llb in
                      let unified = unify pnum llb in
                      return unified llb
                                   
let build_make_app f arg llb = let papp = build_new app_t llb in
                               let _ = build_store app_tag (tag_ref papp llb) llb in
                               let casted_arg = build_bitcast arg unified_ptr "" llb in
                               let _ = build_store casted_arg (arg_ref papp llb) llb in
                               let casted_f = build_bitcast f unified_ptr "" llb in
                               let _ = build_store casted_f (lambda_ref papp llb) llb in
                               let unified = unify papp llb in
                               return unified llb

let ref_scope scope n llb = build_gep scope [| const_i32_t n |] "" llb


let build_get getter llb = match getter with
  | { place = Arg; f = f } -> param f 0
  | { place = Scope n; f = f } -> let scope = Array.get (params f) 1 in
                                  let ptr = ref_scope scope n llb in
                                    build_load ptr "load_from_scope" llb

let lambda_entry () = let body = define_function "" fun_t llm in
                   builder_at_end llc (entry_block body), body

let build_lambda body scope llb = let lambda = build_new lambda_t llb in
                                 let _ = build_store lambda_tag (tag_ref lambda llb) llb in
                                 let _ = build_store body (fun_ref lambda llb) llb in
                                 let _ = build_store scope (scope_ref lambda llb) llb in
                                 let unified = unify lambda llb in
                                 return unified llb

let arg_getter f _ = { place = Arg; f = f }

let make_new_scope body getters llb =
  let len = List.length getters in
  let rec iter n l =
    if n = 0 then l else iter (n - 1) ({ place = Scope (n - 1); f = body }::l) in
    let new_getters = iter len [] in
    let arr = build_array_malloc unified_ptr (const_i32_t len) "scope" llb in
    let scope = build_bitcast (build_gep arr [| zero |] "" llb) scope_t "" llb in 
    List.iter2_exn getters new_getters (fun old fresh ->
      let n = match fresh.place with
        | Scope n -> n
        | _ -> failwith "unbelievable" in
      let src = build_get old llb in
      let dst = ref_scope scope n llb in
      build_store src dst llb |> ignore);
  scope, new_getters
  
let rec make_let vars body = match vars with
  | Sexp.List [] -> body
  | Sexp.List ((Sexp.List [name; binding])::rest) -> 
     Sexp.List [ Sexp.List [ Sexp.Atom "l"; name; make_let (Sexp.List rest) body]; binding ]
  | _ -> failwith "error in let parse"

let rec parse_sexp = function
  | Sexp.Atom x -> (match int_of_string_opt x with
                    | Some n -> Num n
                    | None -> Var x)
  | Sexp.List l -> (match l with
                    | [Sexp.Atom "l"; Sexp.Atom arg; body] -> Lambda(arg, parse_sexp(body))
                    | [f; arg] -> App(parse_sexp(f), parse_sexp(arg))
                    | [Sexp.Atom "let"; vars; body] -> make_let vars body |> parse_sexp
                    | _ -> String.concat ["parse error: "; Sexp.to_string (Sexp.List l)] |> failwith)
                     
                    
let rec compile = function
  | Num x -> { unbound = []; compile = fun _ llb -> build_num (const_i64_t x) llb }
  | Var x -> { unbound = [x]; compile = fun args llb ->
                                        match args with 
                                        | [getter] -> 
                                           (*build_load*) (build_get getter llb) (*"" llb*)
                                        | _ -> failwith "Var wants only 1 binding"
             }
  | App (f_exp, arg_exp) -> let con1 = compile f_exp and
                                con2 = compile arg_exp in
                            let unbound = join con1.unbound con2.unbound in
                            { unbound = unbound;
                              compile = fun getters builder ->
                                        let args1 = collect_args
                                                      unbound
                                                      getters
                                                      con1.unbound and
                                            args2 = collect_args 
                                                      unbound
                                                      getters
                                                      con2.unbound in
                                        let f = con1.compile
                                                  args1
                                                  builder and
                                            arg = con2.compile
                                                    args2
                                                    builder in
                                        build_make_app f arg builder
                            }
  | Lambda (arg, body) -> let con = compile body in
                          let unbound = exclude arg con.unbound in
                          { unbound = unbound;
                            compile = fun getters llb ->
                                      let body_builder, f = lambda_entry () in
                                      let scope, new_getters = make_new_scope f getters llb in
                                      let bound, names  = if List.exists con.unbound
                                                       ~f:(fun x -> x = arg)
                                                  then (arg_getter f
                                                          body_builder)::new_getters, arg::unbound
                                                  else new_getters, unbound in
                                      let bound_ordered = collect_args names bound con.unbound in
                                      let body = con.compile
                                                   bound_ordered
                                                   body_builder in
                                      let _ = build_ret body body_builder in
                                      build_lambda f scope llb
                          }

let build_load_num addr llb = let num = build_bitcast addr num_ptr "" llb in
                              let n_ref = num_ref num llb in
                              build_load n_ref "" llb;;
         
let build_binop build_expr llb = let outer_builder, outer = lambda_entry () in
                                 let arg = arg_getter outer llb in
                                 let inner_builder, inner = lambda_entry () in
                                 let inner_arg = arg_getter inner llb in
                                 let outer_scope = [arg] in
                                 let inner_scope, getters = make_new_scope inner outer_scope llb in
                                 match getters with
                                 | [ outer_arg ] -> undefined ()
                                 | _ -> failwith "Bug: there should be exactly one getter for outer arg";;


let compile_file filename = 
         let s = In_channel.read_all filename |> Sexp.of_string in
         let expr = parse_sexp s in
         let con = compile expr in
         (* building evaluator function *)
         let fty = function_type unified_ptr [| unified_ptr |] in
         let evaluator = define_function "" fty llm in
         let llb = builder_at_end llc (entry_block evaluator) in
         let arg = param evaluator 0 in
         let as_app = build_bitcast arg app_ptr "" llb in
         let tag = build_load (tag_ref as_app llb) "" llb in
         let eval_atom = append_block llc "" evaluator in
         let eval_app = append_block llc "" evaluator in
         let res = build_icmp Icmp.Eq tag app_tag "" llb in
         build_cond_br res eval_app eval_atom llb |> ignore;
         position_at_end eval_atom llb |> ignore;
         build_ret arg llb |> ignore;
         position_at_end eval_app llb |> ignore;
         let callee = build_load (lambda_ref as_app llb) "" llb in
         let lambda = build_bitcast callee lambda_ptr "" llb in
         let scope = build_load (scope_ref lambda llb) "" llb in
         let arg_ptr = arg_ref as_app llb in
         let arg = build_load arg_ptr "" llb in
         let tag = build_load (tag_ref lambda llb) "" llb in
         let simple_app = append_block llc "" evaluator in
         let recursive_app = append_block llc "" evaluator in
         let res = build_icmp Icmp.Eq tag lambda_tag "" llb in
         build_cond_br res simple_app recursive_app llb |> ignore;
         position_at_end simple_app llb |> ignore;
         let f_ptr = fun_ref lambda llb in
         let f = build_load f_ptr "" llb in
         let res = build_call f [| arg; scope |] "" llb in
         let call = build_call evaluator [| res |] "" llb in
         build_ret call llb |> ignore;
         position_at_end recursive_app llb |> ignore;
         let lambda = build_bitcast (build_call evaluator [| callee |] "" llb) lambda_ptr "" llb in
         let scope = build_load (scope_ref lambda llb) "" llb in
         let f_ptr = fun_ref lambda llb in
         let f = build_load f_ptr "" llb in
         let res = build_call f [| arg; scope |] "" llb in
         let call = build_call evaluator [| res |] "" llb in
         build_ret call llb |> ignore;
         let fty = function_type i32_t [| |] in
         let main = define_function "main" fty llm in
         let llb = builder_at_end llc (entry_block main) in
         let e = con.compile [] llb in
         let printf_ty = var_arg_function_type i32_t [| pointer_type i8_t |] in
         let printf = declare_function "printf" printf_ty llm in
         let str = build_global_stringptr "result:  %ld\n" "" llb in
         let str = build_gep str [| zero |] "" llb in
         let res = build_call evaluator [| e |] "" llb in
         let n = build_load_num res llb in
         build_call printf [| str; n |] "" llb |> ignore;
         build_ret zero llb |> ignore;
         print_module "test.ll" llm;
         let ctyp = funptr (void @-> returning int) in
         Llvm_executionengine.initialize () |> ignore;
         let engine = Llvm_executionengine.create llm in
         let f = Llvm_executionengine.get_function_address "main" ctyp engine in
         f () |> ignore


let () = let filename = Sys.argv.(1) in
         compile_file filename
           
