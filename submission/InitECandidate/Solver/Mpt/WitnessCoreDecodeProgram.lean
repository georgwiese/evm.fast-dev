import InitECandidate.Solver.Mpt.WitnessCoreLoopProgram

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

private def callRest : ProgHOL 64→ProgHOL 64 | .decCall _ _ _ _ rest=>rest | _=>.skip
private def yesBranch : ProgHOL 64→ProgHOL 64 | .ite _ yes _=>yes | _=>.skip
private def noBranch : ProgHOL 64→ProgHOL 64 | .ite _ _ no=>no | _=>.skip
def decodeArguments : List (ExpHOL 64):=[localVar "db",localVar "cur_p",localVar "cur_n"]
def decodeField (index : Nat) : ExpHOL 64:=.rfield index (localVar "d")
def afterDecode : ProgHOL 64:=callRest decodeBranch
def decodeTerminal : ProgHOL 64:=yesBranch afterDecode
def decodePush : ProgHOL 64:=noBranch afterDecode
def pushLink : ProgHOL 64:=.store (.op .add [decodeField 1,.const 0#64]) (localVar "top")
def pushTop : ProgHOL 64:=.assign .local (ofString "top") (decodeField 1)
def pushStageTest : ExpHOL 64:=.cmp .equal (.load .one (.op .add [localVar "top",.const 8#64])) (.const 1#64)
def pushSlot : ProgHOL 64:=.ite pushStageTest (.assign .local (ofString "slot") (.const 1#64)) (.assign .local (ofString "slot") (.const 0#64))
def pushMode : ProgHOL 64:=.assign .local (ofString "mode") (.const 2#64)

set_option maxRecDepth 100000
theorem decode_shape : decodeBranch=.decCall (ofString "d") (.comb [.one,.one]) (ofString "_decode_step") decodeArguments afterDecode := by
  simp only [decodeBranch,loopBody,afterLocals,dropDeclarations,body,decodeArguments,afterDecode,callRest,localVar,
    Guest.guestFn__decode_witness_node_body,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
theorem after_decode_shape : afterDecode=.ite (.cmp .equal (decodeField 0) (.const 0#64)) decodeTerminal decodePush := by
  simp only [afterDecode,decodeBranch,decodeTerminal,decodePush,loopBody,afterLocals,dropDeclarations,body,decodeField,callRest,yesBranch,noBranch,localVar,
    Guest.guestFn__decode_witness_node_body,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
theorem terminal_shape : decodeTerminal=.seq (.assign .local (ofString "result") (decodeField 1)) (.assign .local (ofString "mode") (.const 0#64)) := by
  simp only [decodeTerminal,afterDecode,decodeBranch,loopBody,afterLocals,dropDeclarations,body,decodeField,callRest,yesBranch,localVar,
    Guest.guestFn__decode_witness_node_body,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
theorem push_shape : decodePush=.seq pushLink (.seq pushTop (.seq pushSlot pushMode)) := by
  simp only [decodePush,afterDecode,decodeBranch,loopBody,afterLocals,dropDeclarations,body,decodeField,callRest,noBranch,pushLink,pushTop,pushStageTest,pushSlot,pushMode,localVar,
    Guest.guestFn__decode_witness_node_body,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.decode_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.after_decode_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.terminal_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.push_shape
