open Sexplib.Sexp
module Sexp = Sexplib.Sexp
open Expr

let boa_max = int_of_float(2.**62.) - 1;;
let boa_min = -int_of_float(2.**62.);;
let valid_id_regex = Str.regexp "[a-zA-Z][a-zA-Z0-9]*"
let number_regex = Str.regexp "^[+-]?[0-9]+"
let reserved_words = ["let"; "add1"; "sub1"; "isNum"; "isBool"; "if"; "set"; "while"; "def"; "print"]
let reserved_constants = ["true"; "false"; ]
let int_of_string_opt s =
  try Some(int_of_string s) with
  | _ -> None


let rec check_reserve (name : string) =
  let check_reserved_words = List.mem name reserved_words in
  let check_reserved_constants = List.mem name reserved_constants in
  match (check_reserved_words, check_reserved_constants) with
    | (false,false) -> false
    | _ -> true

let rec parse (sexp : Sexp.t) =
  match sexp with
    | Atom(s) -> (match s with 
      | "true" -> EBool(true)
      | "false" -> EBool(false)
      | _ -> (match int_of_string_opt s with
        | Some(i) -> ENumber(i)
        | None -> (match (Str.string_match valid_id_regex s 0) with
          | true -> (match (check_reserve s) with
            | true -> failwith "Invalid" 
            | _ -> EId(s)
          )
          | _ -> (match (Str.string_match number_regex s 0) with
            | true ->  failwith "Non-representable number"
            | _ -> failwith ("Bad variable name " ^ s)
          )
        )
      )
    )
                          
              
    | List(sexps) -> match sexps with 
      | [Atom("add1"); e] -> EPrim1(Add1, parse e)
      | [Atom("sub1"); e] -> EPrim1(Sub1, parse e) 
      | [Atom("isNum"); e] -> EPrim1(IsNum, parse e)
      | [Atom("isBool"); e] -> EPrim1(IsBool, parse e)
      | [Atom("print"); e] -> EPrim1(Print, parse e)
      | [Atom("+"); e1; e2] -> EPrim2(Plus, parse e1, parse e2) 
      | [Atom("-"); e1; e2] -> EPrim2(Minus, parse e1, parse e2) 
      | [Atom("*"); e1; e2] -> EPrim2(Times, parse e1, parse e2) 
      | [Atom("<"); e1; e2] -> EPrim2(Less, parse e1, parse e2) 
      | [Atom(">"); e1; e2] -> EPrim2(Greater, parse e1, parse e2) 
      | [Atom("=="); e1; e2] -> EPrim2(Equal, parse e1, parse e2) 
      | [Atom("if"); e1; e2; e3] -> EIf(parse e1, parse e2, parse e3)
      | Atom("let")::List(bindings_sexp)::exps ->
        (match bindings_sexp with
          | [] -> failwith "Invalid"
          | (_) -> (match exps with
            | [] -> failwith "Invalid"
            | (_) -> let binding_expr = parse_binding bindings_sexp in
                  let p_exps = parse_exps exps in 
                    ELet(binding_expr, p_exps) 
                    )
                )                                                                                                        
      | [Atom("set"); Atom(name); e] -> (match (check_reserve name) with
          | true -> failwith "Invalid" 
          |  _ -> ESet(name, parse e)
        )
      | Atom("while") :: e1 :: es -> EWhile((parse e1), (parse_exps es));
      | Atom(name) :: es -> (match (Str.string_match valid_id_regex name 0) with
        | true -> (match (check_reserve name) with
            | true -> failwith "Invalid" 
            | _ -> EApp(name, (parse_exps es)) ) 
        | _ -> failwith "Invalid"
      )
      | _ -> failwith "Invalid"

and parse_binding binding =
  match binding with 
    | [] -> [] 
    | first::rest -> 
      (match first with 
        | List([Atom(name); e1]) -> (match (check_reserve name) with
          | true -> failwith "Invalid" 
          | _ -> ([(name, parse e1)] @ (parse_binding rest))
          )
        | (_) -> failwith "Invalid"
      )


and parse_typs args : (string * typ) list = (match args with
  | [] -> []
  | Atom(name)::Atom(":")::Atom(typ)::rest -> (match (check_reserve name) with
      | true -> failwith "Invalid" 
      | _ -> (match typ with
          | "Bool" -> (name,TBool) :: (parse_typs rest)
          | "Num" ->  (name,TNum) :: (parse_typs rest)
            | _ -> failwith "Invalid typ"
          )
      )
    
  | _ -> failwith "Invalid parse typ" 
) 


and parse_exps exps =
  match exps with
    | [] -> []
    | first::rest -> [(parse first)] @ (parse_exps rest)

and parse_def sexp = match sexp with
    | List(Atom("def")::(Atom(name))::List(args)::Atom(":")::Atom(ret_type)::es) -> (match (check_reserve name) with
        | true -> failwith "Invalid" 
        | _ -> (match es with 
          | [] -> failwith "Invalid"
          | _-> ( match ret_type with
            | "Bool" -> DFun(name,(parse_typs args),TBool,(parse_exps es))
            | "Num" -> DFun(name,(parse_typs args),TNum,(parse_exps es))
            | _ -> failwith ("Invalid type in def argument: " ^ ret_type)
            ) 
          )
        )
    | _ -> failwith "Invalid"

let rec parse_program sexps =
  match sexps with
  | [] -> failwith "Invalid: Empty program"
  | [e] -> ([], parse e)
  | e::es ->
     let parse_e = (parse_def e) in
     let defs, main = parse_program es in
     parse_e::defs, main
