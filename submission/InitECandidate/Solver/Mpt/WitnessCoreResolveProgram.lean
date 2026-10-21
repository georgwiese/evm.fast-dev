import InitECandidate.Solver.Mpt.WitnessCoreLoopProgram

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

private def decRest : ProgHOL 64→ProgHOL 64 | .dec _ _ _ rest=>rest | _=>.skip
private def callRest : ProgHOL 64→ProgHOL 64 | .decCall _ _ _ _ rest=>rest | _=>.skip
private def yesBranch : ProgHOL 64→ProgHOL 64 | .ite _ yes _=>yes | _=>.skip
private def noBranch : ProgHOL 64→ProgHOL 64 | .ite _ _ no=>no | _=>.skip
def resolveArray : ExpHOL 64:=.load .one (.op .add [localVar "top",.const 24#64])
def resolveArguments : List (ExpHOL 64):=
  [localVar "db",
   .load .one (.op .add [localVar "arr",.panop .mul [localVar "slot",.const 16#64]]),
   .load .one (.op .add [localVar "arr",.panop .mul [localVar "slot",.const 16#64],.const 8#64])]
def resolveCall : ProgHOL 64:=decRest resolveBranch
def afterResolve : ProgHOL 64:=callRest resolveCall
def resolveField (index : Nat) : ExpHOL 64:=.rfield index (localVar "r")
def resolveTerminal : ProgHOL 64:=yesBranch afterResolve
def resolveDecode : ProgHOL 64:=noBranch afterResolve
def resolveHash : ExpHOL 64:=.op .add [localVar "top",.const 80#64]

set_option maxRecDepth 100000
theorem resolve_shape : resolveBranch=.dec (ofString "arr") .one resolveArray resolveCall := by
  simp only [resolveBranch,loopBody,afterLocals,dropDeclarations,body,resolveArray,resolveCall,decRest,localVar,
    Guest.guestFn__decode_witness_node_body,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
theorem resolve_call_shape : resolveCall=.decCall (ofString "r") (.comb [.one,.one,.one,.one]) (ofString "_resolve_step") resolveArguments afterResolve := by
  simp only [resolveCall,afterResolve,resolveBranch,loopBody,afterLocals,dropDeclarations,body,resolveArguments,decRest,callRest,localVar,
    Guest.guestFn__decode_witness_node_body,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
theorem after_resolve_shape : afterResolve=.ite (.cmp .equal (resolveField 0) (.const 0#64)) resolveTerminal resolveDecode := by
  simp only [resolveCall,afterResolve,resolveTerminal,resolveDecode,resolveField,resolveBranch,loopBody,afterLocals,dropDeclarations,body,decRest,callRest,yesBranch,noBranch,localVar,
    Guest.guestFn__decode_witness_node_body,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
theorem resolve_terminal_shape : resolveTerminal=.seq (.store resolveHash (.const 0#64))
    (.seq (.assign .local (ofString "result") (resolveField 1)) (.assign .local (ofString "mode") (.const 0#64))) := by
  simp only [resolveTerminal,resolveCall,afterResolve,resolveField,resolveHash,resolveBranch,loopBody,afterLocals,dropDeclarations,body,decRest,callRest,yesBranch,localVar,
    Guest.guestFn__decode_witness_node_body,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]
theorem resolve_decode_shape : resolveDecode=.seq (.store resolveHash (resolveField 3))
    (.seq (.assign .local (ofString "cur_p") (resolveField 1))
      (.seq (.assign .local (ofString "cur_n") (resolveField 2)) (.assign .local (ofString "mode") (.const 1#64)))) := by
  simp only [resolveDecode,resolveCall,afterResolve,resolveField,resolveHash,resolveBranch,loopBody,afterLocals,dropDeclarations,body,decRest,callRest,noBranch,localVar,
    Guest.guestFn__decode_witness_node_body,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolve_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolve_call_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.after_resolve_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolve_terminal_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.resolve_decode_shape
