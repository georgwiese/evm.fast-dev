import InitECandidate.Solver.Mpt.WitnessCoreProgram
import InitECandidate.Solver.WitnessRadix.ProgramPrefix

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def dropDeclarations : Nat→ProgHOL 64→ProgHOL 64
  | 0,program=>program
  | count+1,.dec _ _ _ rest=>dropDeclarations count rest
  | _,_=>.skip

def afterLocals : ProgHOL 64 := dropDeclarations 7 body
def loopBody : ProgHOL 64 := match afterLocals with | .seq (.while _ program) _=>program | _=>.skip
def condition : ExpHOL 64 := .cmp .notEqual (localVar "go") (.const 0#64)
def footer : ProgHOL 64 := .return (localVar "result")
def initialActions : List WitnessRadix.ProgramPrefix.Action :=
  [.declare "top" (.const 0#64),.declare "result" (.const 0#64),.declare "cur_p" (localVar "p"),.declare "cur_n" (localVar "n"),
    .declare "mode" (.const 1#64),.declare "slot" (.const 0#64),.declare "go" (.const 1#64)]
def decodeBranch : ProgHOL 64 := match loopBody with | .ite _ yes _=>yes | _=>.skip
def resolveBranch : ProgHOL 64 := match loopBody with | .ite _ _ (.ite _ yes _)=>yes | _=>.skip
def returnBranch : ProgHOL 64 := match loopBody with | .ite _ _ (.ite _ _ no)=>no | _=>.skip
def modeTest (mode : BitVec 64) : ExpHOL 64 := .cmp .equal (localVar "mode") (.const mode)

set_option maxRecDepth 100000 in
/-- Literal current236's seven real initial declarations and its actual
explicit-stack loop/return suffix. No alternative executable is introduced. -/
theorem header_shape : body=WitnessRadix.ProgramPrefix.program initialActions (.seq (.while condition loopBody) footer) := by
  simp only [body,Guest.Software.guestFn__decode_witness_node_body,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    WitnessRadix.ProgramPrefix.program,initialActions,afterLocals,dropDeclarations,loopBody,condition,footer,localVar]

set_option maxRecDepth 100000 in
theorem mode_shape : loopBody=.ite (modeTest 1#64) decodeBranch (.ite (modeTest 2#64) resolveBranch returnBranch) := by
  simp only [loopBody,afterLocals,dropDeclarations,body,Guest.Software.guestFn__decode_witness_node_body,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    decodeBranch,resolveBranch,returnBranch,modeTest,localVar]

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.header_shape
#print axioms InitECandidate.Solver.Mpt.WitnessCore.mode_shape
