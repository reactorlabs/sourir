open Instr

(* types of transformations *)
type transform_instructions = analysis_input -> instructions option
type create_optimistic_version = afunction -> version option
type opt_function = afunction -> afunction option
type opt_prog = program -> program option

(* combining transformations *)
let combine_transform_instructions ts ({formals; instrs} as inp : analysis_input) : instructions option =
  let changed, res =
    List.fold_left (fun (changed, inp) t ->
      match t inp with
      | None -> (changed, inp)
      | Some instrs -> (true, {instrs; formals})) (false, inp) ts in
  if changed then Some res.instrs else None

let combine_opt ts inp =
  let changed, res =
    List.fold_left (fun (changed, inp) t ->
      match t inp with
      | None -> (changed, inp)
      | Some out -> (true, out)) (false, inp) ts in
  if changed then Some res else None

let try_opt t inp =
  match t inp with
  | None -> inp
  | Some out -> out

(* generalizing transformations *)
let as_opt_function (transformation : transform_instructions) : opt_function =
  fun func ->
    let version = Instr.active_version func in
    let inp = Analysis.as_analysis_input func version in
    match transformation inp with
    | None -> None
    | Some instrs ->
      let res = {
        label = version.label;
        instrs;
        annotations = None } in
      Some (Instr.replace_active_version func res)

let as_opt_program (transform : opt_function) : opt_prog =
  let transform' instrs =
    match transform instrs with
    | None -> false, instrs
    | Some instrs -> true, instrs in
  fun prog ->
    let changed, main = transform' prog.main in
    let reduce (changed, functions) func =
      let c, f = transform' func in
      (changed||c, f::functions) in
    let changed, functions = List.fold_left reduce (changed, []) prog.functions in
    if changed then Some { functions; main; } else None

let optimistic_as_opt_function (transformation : create_optimistic_version)
                               (cleanup : transform_instructions) : opt_function =
  let cleanup ({instrs} as inp) =
    match cleanup inp with
    | None -> instrs
    | Some instrs -> instrs in
  fun func ->
    match transformation func with
    | None -> None
    | Some version ->
      let inp = Analysis.as_analysis_input func version in
      let cleaned =  cleanup inp in
      let version = { version with instrs = cleaned } in
      Some { func with body = version :: func.body }

(* All available optimizations *)
let cleanup_all_instrs = combine_transform_instructions [
    Transform_cleanup.remove_unreachable_code;
    Transform_cleanup.remove_unused_decl;
    Transform_cleanup.remove_jmp;]
let minimize_liverange_instrs = combine_transform_instructions [
    Transform_cleanup.remove_unused_decl;
    Transform_liveness.minimize_liverange; ]
let const_prop_instrs = combine_transform_instructions [
    Transform_constantfold.const_prop;
    Transform_cleanup.remove_unused_decl;]

let cleanup_all = as_opt_function cleanup_all_instrs
let make_constant = as_opt_function Transform_constantfold.make_constant
let const_prop = as_opt_function const_prop_instrs
let minimize_liverange = as_opt_function minimize_liverange_instrs
let hoist_assignment = as_opt_function Transform_hoist_assign.hoist_assignment
let hoist_drop = as_opt_function Transform_hoist.Drop.apply
let branch_prune = optimistic_as_opt_function
    Transform_assumption.insert_branch_pruning_assumption
    (combine_transform_instructions [
       Transform_cleanup.remove_unreachable_code;
       Transform_cleanup.remove_jmp;])

(* Main optimizer loop *)
exception UnknownOptimization of string

let optimize (opts : string list) (prog : program) : program option =
  let optimizer = function
    | "hoist_assign" ->
      as_opt_program hoist_assignment
    | "hoist_drop" ->
      as_opt_program hoist_drop
    | "min_live" ->
      as_opt_program minimize_liverange
    | "const_prop" ->
      as_opt_program const_prop
    | "make_const" ->
      as_opt_program make_constant
    | "prune" ->
      as_opt_program branch_prune
    | o ->
      raise (UnknownOptimization o)
  in
  let opts =
    if opts = ["all"]
    then ["prune";"make_const";"const_prop";"hoist_assign";"hoist_drop";"min_live"]
    else opts in
  let optimizers = (List.map optimizer opts) @ [(as_opt_program cleanup_all)] in
  let optimizer = combine_opt optimizers in
  optimizer prog
