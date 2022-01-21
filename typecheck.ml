open Expr
open Printf

let rec find ls x =
  match ls with
  | [] -> None
  | (y,v)::rest ->
    if y = x then Some(v) else find rest x

type def_env = (string * (typ list * typ)) list

let build_def_env (defs : def list) : def_env =
  let get_typ (DFun(name, args, ret_typ, body)) = (name, ((List.map snd args), ret_typ)) in
  List.map get_typ defs

let rec tc_e (e : expr) (env : (string * typ) list) (def_env : def_env) : typ =
  let tc_e e env = tc_e e env def_env in 
    match e with
    | ENumber(_) -> TNum
    | EBool(_) -> TBool
    | EId(id) -> (match (find env id) with 
      | None -> failwith ("Variable identifier " ^ id ^ " unbound")
      | Some(t) -> t
    ) 
    | EPrim1(Print, e1) -> (tc_e e1 env)
    | EPrim1(Add1, e1) -> (match (tc_e e1 env) with
      | TNum -> TNum
      | (_) -> failwith "Type mismatch"
    ) 
    | EPrim1(Sub1, e1) -> (match (tc_e e1 env) with
      | TNum -> TNum
      | (_) -> failwith "Type mismatch"
    ) 
    | EPrim1(_, e1) -> let e1c = tc_e e1 env in 
                TBool
    | EPrim2(Less, e1, e2) -> (match (tc_e e1 env) with
      | TNum -> (match (tc_e e2 env) with
          | TNum -> TBool
          | (_) -> failwith "Type mismatch"
        ) 
      | (_) -> failwith "Type mismatch"
      )
    | EPrim2(Greater, e1, e2) -> (match (tc_e e1 env) with
      | TNum -> (match (tc_e e2 env) with
          | TNum -> TBool
          | (_) -> failwith "Type mismatch"
        ) 
      | (_) -> failwith "Type mismatch"
      )
    | EPrim2(Equal, e1, e2) -> let e2_t = (tc_e e2 env) in
      let e1_t = (tc_e e1 env) in
      TBool
    | EPrim2(_, e1, e2) -> (match (tc_e e1 env) with
      | TNum -> (match (tc_e e2 env) with
          | TNum -> TNum
          | (_) -> failwith "Type mismatch"
        ) 
      | (_) -> failwith "Type mismatch"
    ) 
    | EIf(cond, e1, e2) -> (match (tc_e cond env) with
        | TBool -> let t1 = (tc_e e1 env) in 
          let t2 = (tc_e e2 env) in  
          (match t1 with
            | TNum -> ( match t2 with
              | TNum -> TNum
              | _ -> failwith "Type mismatch"
              )
            | TBool -> (match t2 with
              | TBool -> TBool 
              | _ -> failwith "Type mismatch"
          )
            | (_) -> failwith "Type mismatch" 
        )
      | (_) -> failwith "Type mismatch" 
      )
      
    | ELet(bindings, e1) -> (match bindings with
        | [] -> (match e1 with
          | [] -> failwith "Type mismatch empty let"
          | first::[] -> (tc_e first env) 
          | first::rest -> let isValid = (tc_e first env) in  
            tc_e (ELet([],rest)) env
        )
        | (name, e2)::rest -> (tc_e (ELet(rest,e1))((name,(tc_e e2 env))::env))
                  
        )
    | ESet(name, e1) -> let id_v =  tc_e (EId(name)) env in
      let e1_v = tc_e (e1) env in 
      (match id_v with 
        | TBool -> (match e1_v with 
            | TBool -> TBool
            | _ -> failwith "Type mismatch" 
          )
        | TNum -> (match e1_v with
          | TNum -> TNum
          | TBool -> failwith "Type mismatch"
        )
        | (_) -> failwith "Type mismatch"
      )
      
    | EWhile(e1, es) -> let e1_t = (tc_e e1 env) in
      (match e1_t with
        | TBool -> (match es with
          | [] -> TBool
          | first::rest -> let first_t = (tc_e first env) in 
            tc_e (EWhile((EBool(true), rest))) env 
        )
        | (_) -> failwith "Type mismatch"
      ) 
    | EApp(name, es) -> 
      let tc_e1 e1 = (tc_e e1 env) in  
      let check_typs (t,e) = if (t == e) then t else (failwith "Type mismatch") in
      ( match (find def_env name) with
        | Some(ex_typs,ret_typ) -> let es_typs = List.map (tc_e1) es in 
            if ((List.compare_lengths es_typs ex_typs) != 0) then failwith "Type mismatch";
            let compare_list = List.combine es_typs ex_typs in 
            let check_list = List.map check_typs compare_list in
              ret_typ
        | _ -> failwith "Unbound"
      )

     
let tc_def def_env (DFun(name, args, ret_typ, body)) = let tc_body e = tc_e e args def_env in
  let body_typs = List.map (tc_body) body in 
  let last_body_typ = List.hd (List.rev body_typs) in 
    (match ret_typ with 
      | TBool -> (match last_body_typ with 
        | TBool -> TBool
        | _ -> failwith "Type mismatch ret_type1"
      )
      | TNum -> (match last_body_typ with 
        | TNum -> TNum 
        | _ -> failwith "Type mismatch ret_type2" )
      | _ -> failwith "Type mismatch def ret_typ")


let tc_p (defs, main) def_env : typ =
  begin ignore (List.map (tc_def def_env) defs); tc_e main [("input", TNum)] def_env end
