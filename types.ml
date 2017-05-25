open Instr

type analysis_input = {
  formals : VarSet.t;
  instrs : instructions;
}

type transform_instructions = analysis_input -> instructions option
type create_optimistic_version = afunction -> version option
type opt_function = afunction -> afunction option
type opt_prog = program -> program option

