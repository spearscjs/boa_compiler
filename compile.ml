open Printf
open Expr
open Asm
open Typecheck

let boa_max = 4611686018427387903L;;
let boa_min = -4611686018427387904L;;


let rec find ls x =
  match ls with
  | [] -> None
  | (y,v)::rest ->
    if y = x then Some(v) else find rest x

let rec find_def p x =
  match p with
  | [] -> None
  | (DFun(name, args, ret, body) as d)::rest ->
    if name = x then Some(d) else find_def rest x

let stackloc si = RegOffset(-8 * si, RSP)
let heaploc si = RegOffset(8 * si, R15) (* In the kickoff, we store the start of the heap in R15 *)

(* Suggested values for `true` and `false` to distinguish them from pointers *)
let true_const  = HexConst(0x0000000000000006L)
let false_const = HexConst(0x0000000000000002L)
(*
  010
  110
*)
let rec well_formed_e (e : expr) (env : (string * int) list) : string list =
  match e with
  | ENumber(_)
    | EBool(_) -> []
    | EId(x) -> (match find env x with 
        | None -> [("Variable identifier " ^ x ^ " unbound")] 
        | Some(_) -> [] )
    | EPrim1(op,e1) -> well_formed_e e1 env
    | EPrim2(op,e1,e2) -> (well_formed_e e1 env) @ (well_formed_e e2 env) 
    | ELet(bindings, e) -> (match bindings with
      | [] -> (match e with
        | [] -> [] 
        | first::rest -> (well_formed_e first env) @ (well_formed_e (ELet([],rest)) env)
      )
      | (name, e1)::rest -> let found = find_binding name rest in 
              (match found with 
                | false -> (well_formed_e e1 env) @ well_formed_e (ELet(rest,e)) ((name,0)::env) 
                | true -> ["Multiple bindings for variable identifier " ^ name]
              )
      )
    | ESet(name, e1) -> (well_formed_e (EId(name)) env) @ (well_formed_e e1 env) 
    | EIf(cond, e1, e2) -> (well_formed_e cond env) @ (well_formed_e e1 env) @ (well_formed_e e2 env) 
    | EWhile(e1, es) -> (well_formed_e e1 env) @ (match es with
      | [] -> []
      | first::rest -> (well_formed_e first env) @ (well_formed_e (EWhile(e1,rest)) env)
      )
    | EApp(name, es) -> (well_formed_body es env)
    | _ -> failwith "Not yet implemented2"
  

 and find_binding (name : string) bindings : bool = (match bindings with 
  | [] -> false
  | (bn,_)::rest ->  if (bn = name) then true 
                          else find_binding name rest 
)  

and well_formed_body body env = match body with
| [] -> []
| first::rest -> (well_formed_e first env) @ (well_formed_body rest env) 

let rec well_formed_args args = match args with 
| [] -> []
| first::rest -> let found = List.mem first rest in
  (match found with
    | true -> ["Multiple bindings"] @ (well_formed_args rest )
    | _ -> well_formed_args rest
  )

let well_formed_def (DFun(name, args, ret, body)) = 
  let make_env (n,t) = (n,0) in 
    let arg_env = (List.map make_env args) in
    (well_formed_args arg_env) @ (well_formed_body body arg_env)


let rec find_dups ls = (match ls with
  | [] -> []
  | first::rest -> if (List.mem first rest) then (failwith "Multiple functions") else (find_dups rest)
)

let well_formed_prog (defs, main) =
  let make_def (DFun(name,_,_,_)) = name in
  let def_names = List.map make_def defs in
  let well_f_defs = well_formed_args def_names in
  let dup_name = find_dups def_names in
  well_f_defs @ dup_name @ (List.concat (List.map well_formed_def defs)) @ (well_formed_e main [("input", 1)])
  
 
let check p : string list =
  match well_formed_prog p with
  | [] -> []
  | errs -> failwith (String.concat "\n" errs)


let rec improve_expr (e : expr) : expr =
    let folded = c_fold e in
    let propped = c_prop folded in 
    if (propped = e) then e else (improve_expr propped)

and c_fold (e : expr) : expr = match e with  
    | EPrim1(Add1, ENumber(n1)) ->  let n1_64 = Int64.of_int(n1) in
      let n2_64 = Int64.of_int(1) in
      let n3_64 = (Int64.add n1_64 n2_64) in
      if (((Int64.compare n3_64 boa_max) > 0) || ((Int64.compare n3_64 boa_min) < 0 )) then e else ENumber(n1 + 1)
    | EPrim1(Add1, e) -> EPrim1(Add1, (c_fold e))

    | EPrim1(Sub1, ENumber(n1)) ->  let n1_64 = Int64.of_int(n1) in
      let n2_64 = Int64.of_int(1) in
      let n3_64 = (Int64.sub n1_64 n2_64) in
      if (((Int64.compare n3_64 boa_max) > 0) || ((Int64.compare n3_64 boa_min) < 0 )) then e else ENumber(n1 - 1)
    | EPrim1(Sub1, e) -> EPrim1(Sub1, (c_fold e))

    | EPrim1(IsNum, ENumber(_)) -> EBool(true)
    | EPrim1(IsNum, EBool(_)) -> EBool(false)
    | EPrim1(IsNum, e) -> EPrim1(IsNum, (c_fold e))

    | EPrim1(IsBool, EBool(_)) -> EBool(true)
    | EPrim1(IsBool, ENumber(_)) -> EBool(false)
    | EPrim1(IsBool, e) -> EPrim1(IsBool, (c_fold e))

    | EPrim1(Print, e) -> EPrim1(Print,(c_fold e))

    | EPrim2(Plus, ENumber(n1), ENumber(n2)) ->  let n1_64 = Int64.of_int(n1) in
      let n2_64 = Int64.of_int(n2) in
      let n3_64 = (Int64.add n1_64 n2_64) in
      if (((Int64.compare n3_64 boa_max) > 0) || ((Int64.compare n3_64 boa_min) < 0 )) then e else ENumber(n1 + n2)
    | EPrim2(Plus, e1, e2) -> EPrim2(Plus, (c_fold e1), (c_fold e2))

    | EPrim2(Minus, ENumber(n1), ENumber(n2)) ->  let n1_64 = Int64.of_int(n1) in
      let n2_64 = Int64.of_int(n2) in
      let n3_64 = (Int64.sub n1_64 n2_64) in
      if (((Int64.compare n3_64 boa_max) > 0) || ((Int64.compare n3_64 boa_min) < 0 )) then e else ENumber(n1 - n2)
    | EPrim2(Minus, e1, e2) -> EPrim2(Minus, (c_fold e1), (c_fold e2))

    | EPrim2(Times, ENumber(n1), ENumber(n2)) ->  let n1_64 = Int64.of_int(n1) in
      let n2_64 = Int64.of_int(n2) in
      let n3_64 = (Int64.mul n1_64 n2_64) in
      if (((Int64.compare n3_64 boa_max) > 0) || ((Int64.compare n3_64 boa_min) < 0 )) then e else ENumber(n1 * n2)
    | EPrim2(Times, e1, e2) -> EPrim2(Times, (c_fold e1), (c_fold e2))

    | EPrim2(Less, ENumber(n1), ENumber(n2)) ->  let n1_64 = Int64.of_int(n1) in
      let n2_64 = Int64.of_int(n2) in
      let n3_64 = (Int64.compare n1_64 n2_64) in
      (if (n3_64 < 0) then EBool(true) else EBool(false))
    | EPrim2(Less, e1, e2) -> EPrim2(Less, (c_fold e1), (c_fold e2))

    | EPrim2(Greater, ENumber(n1), ENumber(n2)) ->  let n1_64 = Int64.of_int(n1) in
      let n2_64 = Int64.of_int(n2) in
      let n3_64 = (Int64.compare n1_64 n2_64) in
      (if (n3_64 > 0) then EBool(true) else EBool(false))
    | EPrim2(Greater, e1, e2) -> EPrim2(Greater, (c_fold e1), (c_fold e2))

    | EPrim2(Equal, ENumber(n1), ENumber(n2)) ->  let n1_64 = Int64.of_int(n1) in
      let n2_64 = Int64.of_int(n2) in
      let n3_64 = (Int64.compare n1_64 n2_64) in
      (if (n3_64 = 0) then EBool(true) else EBool(false))
    | EPrim2(Equal, e1, e2) -> EPrim2(Equal, (c_fold e1), (c_fold e2))


    | EIf(EBool(true), thn, els) -> c_fold thn
    | EIf(EBool(false), thn, els) -> c_fold els
    | EIf(cond, thn, els) -> EIf((c_fold cond), (c_fold thn), (c_fold els))

    | ELet(bs,es) -> let f (a,b) = (a,c_fold b) in (outer_selection (ELet((List.map f bs), (body_selection (List.map c_fold es)))))

    | EWhile(EBool(false), es) -> EBool(false)
    | EWhile(cond,es) -> EWhile((c_fold cond), (body_selection (List.map c_fold es)))

    | _ -> e

and outer_selection (e : expr) = match e with
  | ELet(bs,es) -> (match es with
    | ENumber(i) :: [] -> ENumber(i)
    | EBool(b) :: [] -> EBool(b)
    | _ -> e
  )
  | EWhile(EBool(false),es) -> EBool(false)
  | _ -> e

and body_selection (es : (expr list)) = (match es with
  | [] -> []
  | last::[] -> (match last with 
    | ELet(bs,es) -> [ELet(bs, (body_selection es))]
    | EWhile(cond,es) -> [EWhile(cond, (body_selection es))]  
    | _ -> [last]
  )
  | first::rest -> (match first with
    | ENumber(_) -> (body_selection rest)
    | EBool(_) -> (body_selection rest)
    | ELet(bs,es) -> ELet(bs, (body_selection es)) :: (body_selection rest)
    | _ -> first :: (body_selection rest)
  )
)
and replace (name : string) (binding_expr : expr) (e : expr)  : expr = 
  match e with
      | EId(x) -> if (x = name) then binding_expr else e
      | EPrim2(op,e1,e2) -> EPrim2(op,(replace name binding_expr e1), (replace name binding_expr e2))
      | EPrim1(op,e1) -> EPrim1(op,(replace name binding_expr e1))
      | EIf(cond,thn,els) -> EIf((replace name binding_expr cond),(replace name binding_expr thn), (replace name binding_expr els))
      | ELet(bs,es) -> let bs = (replace_args name binding_expr bs) in (ELet(bs, (List.map (replace_xs bs) es)))
      | EWhile(cond,es) -> EWhile((replace name binding_expr cond),(List.map (replace_xs [(name,binding_expr)]) es))
      | _ -> e
    

and replace_args name be bs = 
   match bs with
   | [] -> []
   | (name,e)::rest -> (name, (replace name be e)) :: (replace_args name be rest)

and replace_xs bindings exp = (match bindings with
  | [] -> exp 
  | (name,e)::rest -> (match exp with 
    | ELet(bs,es) -> let f (a,b) = (a, (replace name e b)) in ELet((List.map f bs), (replace_es bs es))
    | _ -> replace_xs rest (replace name e exp)   
  )
)

and replace_es bs es = match es with
  | [] -> []
  | first::rest -> (match first with 
    | ELet(be,bv) -> let f (a,b) = (a,(replace_xs bs b)) in (replace_xs bs (ELet((List.map f be), bv))) :: (replace_es bs rest)
    | _ -> (replace_xs bs first) :: (replace_es bs rest)
  )
and contains_set (e : expr) = (match e with
  | ENumber(_) -> false
  | EBool(_) -> false
  | EId(x) -> false
  | EIf(e1,e2,e3) -> (match ((contains_set e1),(contains_set e2), (contains_set e3)) with
    | (false, false, false) -> false
    | _ -> true
  )
  | ELet(bs,es) -> contains_set_l es
  | ESet(_,_) -> true
  | EPrim1(_,e1) -> contains_set e1
  | EWhile(e1,es) -> (match ((contains_set e1),(contains_set_l es)) with
    | (false, false) -> false
    | _ -> true
  )
  | EPrim2(_,e1,e2) -> (match ((contains_set e1),(contains_set e2)) with
    | (false, false) -> false
    | _ -> true
  )
  | _ -> true
)
and contains_set_l es = match es with
  | [] -> false
  | first::rest -> if (contains_set first) then true else (contains_set_l rest)
  
and c_prop (e : expr) : expr = if (contains_set e) then e 
  else (match e with
    | ELet(bs,es) -> ELet(bs, (replace_es bs es))
    | _ -> e
  )


let rec compile_expr (e : expr) (si : int) (env : (string * int) list) def_env
  : instruction list =
  let compile_expr e si env = compile_expr e si env def_env in 
  let compile_exprs e si env = compile_exprs e si env def_env in 
  let compile_prim1 op e si env = compile_prim1 op e si env def_env in
  let compile_prim2 op e1 e2 si env = compile_prim2 op e1 e2 si env def_env in
  let isB = gen_temp "is_bool" in 
  let isB_end = gen_temp "end_isB" in 
  let isBool =  [(ICmp (Reg(RAX), Const(2))); (IJe isB); (IMov (Reg(RAX), (stackloc si))); (ICmp (Reg(RAX),(Const(6)))); (IJe isB); (IMov (Reg(RAX), Const(2))); (IJmp isB_end); (ILabel isB); (IMov (Reg(RAX),(Const(6)))); (ILabel isB_end)] in
  let revert_bool = [(IShr (Reg(RAX), Const(2))); (IShl (Reg(RAX), Const(1)))] in
  match e with 
    | EId(x) -> (match find env x with
            | None -> []
            | Some(i) -> [(IMov ((Reg(RAX), stackloc i)))] )
    | ENumber(i) -> let i64 = Int64.of_int(i) in [(IMov ((Reg(RAX)), (Const64((Int64.add (Int64.mul i64 2L) 1L)))))] 
    | EBool(true) -> [(IMov ((Reg(RAX)),true_const))] 
    | EBool(false) -> [(IMov ((Reg(RAX)),false_const))]
    | EPrim1(op, e) -> compile_prim1 op e si env 
    | EPrim2(op, e1, e2) -> compile_prim2 op e1 e2 si env
    | ELet((bindings), es) -> (match bindings with 
      | [] -> compile_exprs es si env           
      | (name, e1)::rest -> (compile_expr (improve_expr e1) si env) @ [(IMov ((stackloc (si)),(Reg(RAX))))] @ (compile_expr (ELet(rest,es)) (si+1) ((name, si)::env)) 
    ) 
    | EIf(cond, e1, e2) -> 
      let else_label = gen_temp "else" in 
      let end_label = gen_temp "end" in 
      (compile_expr cond si env) @ [(ICmp ((Reg(RAX), (Const(6))))); (IJne else_label)] @ (compile_expr e1 (si+1) env) @ [(IJmp end_label); (ILabel else_label)] @ (compile_expr e2 (si+2) env) @ [(ILabel end_label)] 
    | ESet(name, e1) -> let name_si = find env name in 
      (match name_si with 
        | Some(n_si) -> (compile_expr e1 (si) env) @ [(IMov ((stackloc (n_si)), (Reg(RAX))))]
        | None -> failwith "Unbound"
      )
    | EWhile(e1, es) -> let s_label = (gen_temp "start_while") in
        let e_label = (gen_temp "end_while")  in
        [(ILabel s_label)] @ (compile_expr e1 si env) @ revert_bool @ [(IJe e_label)] @ (compile_exprs es (si) env) @ [(IJmp s_label)] @ [(ILabel e_label)] @ [(IMov ((Reg(RAX)),false_const))]
    | EApp(name, args) -> 
      let num_args = List.length args in
      let args_is = compile_args args si env def_env in 
      let si_above_args = si + (num_args) in
      let after_label = gen_temp "after_call" in
      args_is @  [(IMov (Reg(RAX), Label(after_label))); (IMov ((stackloc si_above_args), Reg(RAX))); (IMov ((stackloc (si_above_args+1)), Reg(RSP))); (ISub (Reg(RSP), (Const(8*(num_args+si))))); (IJmp name)] 
       @ [(ILabel after_label); (IMov ((Reg(RSP), (stackloc (2)))))] 
       

and compile_exprs exprs si env def_env = match exprs with
| [] -> []
| first::rest -> (compile_expr first si env def_env) @ (compile_exprs rest si env def_env)

and compile_args exprs si env def_env = match exprs with
| [] -> []
| first::rest -> (compile_expr (improve_expr first) si env def_env) @ [(IMov ((stackloc si), (Reg(RAX))))] @ (compile_args rest (si+1) env def_env)


and compile_prim1 op e si env def_env =
  let compile_prim1 op e si env = compile_prim1 op e si env def_env in
  let iShl_rax = [(IShl (Reg(RAX), (Const(1))))] in 
  let store_e1 = [(IMov ((stackloc si), (Reg(RAX))))] in
  let arg_exprs = compile_expr e si env def_env in
  let update_bool = [(IAdd (Reg(RAX),Const(1)))] @ iShl_rax in
  let isB = gen_temp "is_bool" in 
  let isB_end = gen_temp "end_isB" in 
    match op with
      | Add1 -> arg_exprs @ store_e1 @ [(IAdd ((Reg(RAX)), (Const(2)))); (IJo "oflow_error")] 
      | Sub1 -> arg_exprs @ store_e1 @ [(ISub ((Reg(RAX)), (Const(2)))); (IJo "oflow_error")] 
      | IsNum -> arg_exprs @ [(IAnd ((Reg(RAX)), (Const(1))))] @ iShl_rax @ update_bool
      | IsBool -> arg_exprs @ store_e1 @ [(ICmp (Reg(RAX), Const(2))); (IJe isB); (IMov (Reg(RAX), (stackloc si))); (ICmp (Reg(RAX),(Const(6)))); (IJe isB); (IMov (Reg(RAX), Const(2))); (IJmp isB_end); (ILabel isB); (IMov (Reg(RAX),(Const(6)))); (ILabel isB_end)]
      | Print -> arg_exprs @ store_e1 @ [(ISub (Reg(RSP), Const(16))); (IMov (Reg(RDI), Reg(RAX))); (ICall "print"); (IAdd (Reg(RSP), Const(16))); (IMov (Reg(RAX), (stackloc si)))] 
      | _ -> failwith "ERROR: unknown op found during compilation"

and compile_prim2 op e1 e2 si env def_env =
  let compile_prim2 op e1 e2 si env = compile_prim2 op e1 e2 si env def_env in
  let e1is = compile_expr e1 si env def_env in 
  let e2is = compile_expr e2 (si+1) env def_env in
  let store_e1 = [(IMov ((stackloc si), (Reg(RAX))))] in 
  let store_e2 = [(IMov ((stackloc (si+1)), (Reg(RAX))))] in 
  let revert_rax = [(IMul (Reg(RAX), (Const(2)))); (IJo "oflow_error"); (IAdd (Reg(RAX), Const(1))); (IJo "oflow_error")] in
  let iSar_rax = [(ISar (Reg(RAX), (Const(1))))] in 
  let iShl_rax = [(IShl (Reg(RAX), (Const(1))))] in 
  let update_bool = [(IAdd (Reg(RAX),Const(1)))] @ iShl_rax in
  let revert_bool = [(IShr (Reg(RAX), Const(2))); (IShl (Reg(RAX), Const(1)))] in
  match op with    
          | Plus -> e1is  @ iSar_rax @ store_e1 @ e2is  @ iSar_rax @ store_e2 @ [(IAdd ((Reg(RAX)), (stackloc si))); (IJo "oflow_error")] @ revert_rax
          | Minus -> e1is  @ iSar_rax @ store_e1 @ e2is @ iSar_rax @ store_e2 @ [((IMov ((Reg(RAX)), (stackloc si)))); (ISub ((Reg(RAX)), (stackloc (si+1)))); (IJo "oflow_error")] @ revert_rax
          | Times -> e1is  @ iSar_rax @ store_e1 @ e2is @ iSar_rax @ store_e2 @ [((IMov ((Reg(RAX)), (stackloc si)))); (IMul ((Reg(RAX)), (stackloc (si+1)))); (IJo "oflow_error")] @ revert_rax
          | Less -> e1is @ store_e1 @ e2is @ store_e2 @ (compile_prim2 Minus e1 e2 si env) @ [(IShr (Reg(RAX), (Const(62))))] @ [(IAnd (Reg(RAX), (HexConst(0x0000000000000002L))))] @ update_bool
          | Greater -> (compile_prim2 Less e2 e1 si env)
          | Equal -> (compile_prim2 Less e1 e2 si env) @ revert_bool @ store_e1 @ (compile_prim2 Greater e1 e2 (si+1) env) @ revert_bool @ [((IAdd ((Reg(RAX)), (stackloc si)))); (IXor ((Reg(RAX), Const(2))))] @ update_bool
          | _ -> failwith "ERROR: unknown op found during compilation"

and compile_def (DFun(name, args, ret, body)) def_env =  
  let env = create_args_env (List.rev args) 0 in 
  let b_is = compile_def_exprs body 2 env def_env in
  [(ILabel name)] @ b_is @ [(IRet)]



and compile_def_exprs exprs si env def_env = match exprs with
| [] -> []
| first::rest -> (match first with 
  | ELet(bs,es) -> (match contains_set_l es with 
    | true -> (compile_expr first si env def_env) @ (compile_def_exprs rest si env def_env)
    | false -> (compile_expr (improve_expr first) si env def_env) @ (compile_def_exprs rest si env def_env)
    )
  | _ -> (compile_expr (improve_expr first) si env def_env) @ (compile_exprs rest si env def_env)
)

and create_args_env args si = match args with
  | [] -> []
  | (name,_)::rest -> [(name,(si-1))] @ (create_args_env rest (si-1))

let compile_to_string ((defs, main) as prog : Expr.prog) =
  let _ = check prog in
  let def_env = build_def_env defs in
  let _ = tc_p prog def_env in
  let compiled_defs = List.concat (List.map (fun d -> compile_def d defs) defs) in
  let compiled_main = compile_expr (improve_expr main) 2 [("input", 1)] defs in
  let prelude = "  section .text\n" ^
                "  extern error\n" ^
                "  extern print\n" ^
                "  global our_code_starts_here\n" in
  let kickoff = "our_code_starts_here:\n" ^
                "push rbx\n" ^
                "  mov r15, rdi\n" ^       (* rdi and r15 contain a pointer to the start of the heap *)
                "  mov [rsp - 8], rsi\n" ^ (* rsi and [rsp-8] contain the input value *)
                to_asm compiled_main ^
                "\n  pop rbx\nret\n" in
  let postlude = [IRet; (ILabel "t_n_error"); (IMov (Reg(RAX), (Const(1)))); (IJmp "error_call"); (ILabel "t_b_error"); (IMov (Reg(RAX), (Const(2)))); (IJmp "error_call"); (ILabel "oflow_error"); (IMov (Reg(RAX), (Const(0)))); (IJmp "error_call"); (ILabel "error_call"); (ISub (Reg(RSP), Const(16))); (IMov (Reg(RDI), Reg(RAX))); (ICall "error"); (IAdd (Reg(RSP), Const(16)))]
    (* TODO *) in
  let as_assembly_string = (to_asm (compiled_defs @ postlude)) in
  sprintf "%s%s\n%s\n" prelude as_assembly_string kickoff
