open Instr
open Types

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
    let changed, main =
      transform' prog.main
    in
    let reduce (changed, functions) func =
      let c, f = transform' func in
      (changed||c, f::functions) in
    let changed, functions = List.fold_left reduce (changed, []) prog.functions in
    let functions = List.rev functions in
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
let const_fold_instrs = combine_transform_instructions [
    Transform_constantfold.const_fold;
    Transform_cleanup.remove_unused_decl;]
let normalize_graph_instrs = combine_transform_instructions [
    Transform_fix.remove_falltrough;
    Transform_fix.make_branch_targets_unique;]

let cleanup_all = as_opt_function cleanup_all_instrs
let const_fold = as_opt_function const_fold_instrs
let minimize_liverange = as_opt_function minimize_liverange_instrs
let hoist_assignment = as_opt_function Transform_hoist_assign.hoist_assignment
let hoist_drop = as_opt_function Transform_hoist.Drop.apply
let branch_prune = optimistic_as_opt_function
    (Transform_prune.insert_branch_pruning_assumption)
    (combine_transform_instructions [
       Transform_prune.branch_prune;
       Transform_cleanup.remove_unreachable_code;])
let branch_prune_no_hoist = optimistic_as_opt_function
    (Transform_prune.insert_branch_pruning_assumption ~hoist:false)
    (combine_transform_instructions [
       Transform_prune.branch_prune;
       Transform_cleanup.remove_unreachable_code;])
let normalize_graph = as_opt_program (as_opt_function normalize_graph_instrs)

(* Main optimizer loop *)
exception UnknownOptimization of string

let all_opts = ["prune";
                "prune_no_hoist";
                "hoist_osr";
                "const_fold";
                "hoist_assign";
                "hoist_drop";
                "min_live";
                "inline_small"]
let manual_opts = ["inline_med";
                   "inline_max"]

let optimize (opts : string list) (prog : program) : program option =
  let optimizer = function
    | "hoist_assign" ->
      as_opt_program hoist_assignment
    | "hoist_drop" ->
      as_opt_program hoist_drop
    | "min_live" ->
      as_opt_program minimize_liverange
    | "const_fold" ->
      as_opt_program const_fold
    | "prune_no_hoist" ->
      as_opt_program branch_prune_no_hoist
    | "prune" ->
      as_opt_program branch_prune
    | "hoist_osr" ->
      as_opt_program (as_opt_function Transform_assumption.hoist_assumption)
    | "inline_max" ->
      Transform_inline.inline ()
    | "inline_med" ->
      Transform_inline.inline ~max_depth:4 ~max_size:220 ()
    | "inline_small" ->
      Transform_inline.inline ~max_depth:2 ~max_size:170 ()
    | o ->
      raise (UnknownOptimization o)
  in
  let optimizers = (List.map optimizer opts) @ [(as_opt_program cleanup_all)] in
  let optimizer = combine_opt optimizers in

  let optimizer =
    combine_opt [
        (as_opt_program Transform_assumption.insert_checkpoints);
        optimizer;
        Transform_assumption.remove_empty_osr;
        optimizer;
      ]
  in
  optimizer prog
