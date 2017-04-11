open Instr

(* types of transformations *)
type transform_instructions = instruction_stream -> instruction_stream option
type create_optimistic_version = afunction -> version option
type opt_function = afunction -> afunction option
type opt_prog = program -> program option

(* combining transformations *)
let (&&&) t2 t1 instrs =
  match t1 instrs with
  | None -> t2 instrs
  | Some instrs ->
    begin match t2 instrs with
      | None -> Some instrs
      | Some instrs -> Some instrs
    end

let (!!) t instrs =
  match t instrs with
  | None -> false, instrs
  | Some instrs -> true, instrs

let (!!!) t instrs =
  let _, instrs = !! t instrs in instrs

(* generalizing transformations *)
let as_opt_function (transformation : transform_instructions) : opt_function =
  fun func ->
    let version = Instr.active_version func in
    let instrs = version.instrs in
    match transformation instrs with
    | None -> None
    | Some instrs ->
      let res = {
        label = version.label;
        instrs;
        annotations = None } in
      Some (Instr.replace_active_version func res)

let as_opt_program (transformation : opt_function) : opt_prog =
  fun prog ->
    let changed, main = !! transformation prog.main in
    let reduce (changed, functions) func =
      let c, f = !! transformation func in
      (changed||c, f::functions) in
    let changed, functions = List.fold_left reduce (changed, []) prog.functions in
    if changed then Some { functions; main; } else None

let optimistic_as_opt_function (transformation : create_optimistic_version)
                               (cleanup : transform_instructions) : opt_function =
  fun func ->
    match transformation func with
    | None -> None
    | Some version ->
      let _, cleaned = !! cleanup version.instrs in
      let version = { version with instrs = cleaned } in
      Some { func with body = version :: func.body }

(* All available optimizations *)
let cleanup_all_instrs =
  (Transform_cleanup.remove_jmp &&&
   (Transform_cleanup.remove_unused_label &&&
    (Transform_cleanup.remove_unused_decl &&&
     Transform_cleanup.remove_unreachable_code)))
let minimize_liverange_instrs = Transform_liveness.minimize_liverange &&& Transform_cleanup.remove_unused_decl
let const_prop_instrs = Transform_cleanup.remove_unused_decl &&& Transform_constantfold.const_prop

let cleanup_all = as_opt_function cleanup_all_instrs
let const_prop = as_opt_function const_prop_instrs
let minimize_liverange = as_opt_function minimize_liverange_instrs
let hoist_assignment = as_opt_function Transform_hoist_assign.hoist_assignment
let hoist_drop = as_opt_function Transform_hoist.Drop.apply
let branch_prune = optimistic_as_opt_function
    Transform_assumption.insert_branch_pruning_assumption
    (Transform_cleanup.remove_jmp &&& Transform_cleanup.remove_unreachable_code)

(* Main optimizer loop *)
exception UnknownOptimization of string

let optimize (opts : string list) (prog : program) : program option =
  let rec optimizer (acc : opt_prog) o =
    match o with
    | [] ->
      acc &&& (as_opt_program cleanup_all)
    | "hoist_assign"::r ->
      acc &&& (as_opt_program hoist_assignment)
    | "hoist_drop"::r ->
      acc &&& (as_opt_program hoist_drop)
    | "min_live"::r ->
      acc &&& (as_opt_program minimize_liverange)
    | "const_prop"::r ->
      acc &&& (as_opt_program const_prop)
    | "prune"::r ->
      acc &&& (as_opt_program branch_prune)
    | o::r ->
      raise (UnknownOptimization o)
  in
  let id p = Some p in
  let optimizer = if opts = ["all"]
    then optimizer id ["prune";"const_prop";"hoist_assign";"hoist_drop";"min_live"] else optimizer id opts in
  optimizer prog

