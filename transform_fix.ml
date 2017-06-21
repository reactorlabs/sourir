open Instr
open Transform_utils
open Types

let remove_falltrough ({instrs} as inp : analysis_input) =
  let normalize pc =
    let fresh_label label tag = (Edit.fresh_label instrs (label ^ "_" ^ tag)) in
    let has_fallthrough pc =
      match instrs.(pc-1) with
      | Guard_hint _ | Decl_var _ | Decl_array _
      | Assign _ | Array_assign _
      | Drop _ | Read _ | Call _ | Label _
      | Comment _ | Osr _ | Print _ | Assert _ -> true
      | Stop _ | Return _ | Goto _ | Branch _ -> false
    in
    match[@warning "-4"] instrs.(pc) with
    | Label (MergeLabel l) ->
        if has_fallthrough pc
        then InsertBeforeLabel [ Goto l ]
        else Unchanged
    | Label (BranchLabel l) ->
        let l' = fresh_label l (string_of_int pc) in
        if has_fallthrough pc
        then ReplaceLabel [ Goto l';
                            Label (BranchLabel l); Goto l';
                            Label (MergeLabel l') ]
        else Unchanged
    | _ -> Unchanged
  in
  change_instrs normalize inp

let make_branch_targets_unique ({instrs} as inp : analysis_input) =
  let normalize pc =
    let incoming_branches label =
      (* should not rely on preds on a broken graph *)
      let rec incoming pc =
        if pc = Array.length instrs then [] else
        match[@warning "-4"] instrs.(pc) with
        | Branch (_, l1, l2) when l1 = label && l2 = label ->
            pc :: pc :: incoming (pc+1)
        | Branch (_, l1, l2) when l1 = label || l2 = label ->
            pc :: incoming (pc+1)
        | _-> incoming (pc+1)
      in
      incoming 0
    in
    let fresh_label label tag = (Edit.fresh_label instrs (label ^ "_" ^ tag)) in
    match[@warning "-4"] instrs.(pc) with
    | Label (BranchLabel l) ->
        if List.length (incoming_branches l) > 1
        then ReplaceLabel [ Label (MergeLabel l) ]
        else Unchanged
    | Branch (e, l1, l2) ->
        let i1, i2 = incoming_branches l1, incoming_branches l2 in
        begin match i1, i2 with
        | _, [] -> assert(false)
        | [], _ -> assert(false)
        | [pc1], [pc2] ->
            assert(pc1 = pc && pc2 = pc);
            assert (l1 <> l2);
            Unchanged
        | [pc1], _ ->
            assert(pc1 = pc);
            let l2' = fresh_label l2 (string_of_int pc) in
            Replace [ Branch (e, l1, l2'); Label (BranchLabel l2'); Goto l2 ]
        | _, [pc2] ->
            assert(pc2 = pc);
            let l1' = fresh_label l1 (string_of_int pc) in
            Replace [ Branch (e, l1', l2); Label (BranchLabel l1'); Goto l1 ]
        | _, _ ->
            (* It might still be that l1 = l2.
             * To avoid creating a duplicated label we tag with l/r *)
            let l1' = fresh_label l1 ((string_of_int pc) ^ "l") in
            let l2' = fresh_label l2 ((string_of_int pc) ^ "r") in
            Replace [ Branch (e, l1', l2');
                      Label (BranchLabel l1'); Goto l1;
                      Label (BranchLabel l2'); Goto l2 ]
        end
    | _ -> Unchanged
  in
  change_instrs normalize inp
