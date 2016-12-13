open Instr

let disassemble prog =
  let lit_to_str lit =
    match lit with
    | Int i -> string_of_int i
    | Bool b -> string_of_bool b
    | Nil -> "nil"
  in
  let op_to_str op =
    match op with
    | Eq -> "eq"
    | Plus -> "plus"
  in
  let exp_to_str exp =
    match exp with
    | Var v -> v
    | Lit lit -> lit_to_str lit
    | Op (op, vars) ->
        "(" ^ op_to_str op ^ " " ^ String.concat " " vars ^ ")"
    in
  let instr_to_str instr =
    match instr with
    | Decl_const (var, exp)           -> " cns " ^ var ^ " := " ^ exp_to_str exp
    | Decl_mut (var, exp)             -> " mut " ^ var ^ " := " ^ exp_to_str exp
    | Assign (var, exp)               -> " ass " ^ var ^ " := " ^ exp_to_str exp
    | Branch (exp, l1, l2)            -> " brt " ^ exp_to_str exp ^ " ? " ^ l1 ^ " " ^ l2
    | Label label                     -> label ^ ":"
    | Goto label                      -> " gto " ^ label
    | Print exp                       -> " prn " ^ exp_to_str exp
    | Invalidate (exp, l, vars)       -> " inv " ^ exp_to_str exp ^ " ? " ^ l ^ " (" ^ String.concat " " vars ^ ")"
    | Stop                            -> " stp"
    | Comment string                  -> " # " ^ string
  in
  (* TODO: this looks ugly... *)
  String.concat "\n" (Array.to_list (Array.map instr_to_str prog))
