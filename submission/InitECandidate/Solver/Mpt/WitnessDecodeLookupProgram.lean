import InitECandidate.Solver.Mpt.WitnessDecodeRootProgram

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def missingTest : ExpHOL 64 := .cmp .equal (.rfield 0 (localVar "r")) (.const 0#64)
def missingCall : ProgHOL 64 := .call (some (none,none)) (ofString "mpt_fail") [.const 1#64]
def missingGuard : ProgHOL 64 := .ite missingTest missingCall .skip
def materializeCall : ProgHOL 64 := match afterLookup with | .seq _ rest=>rest | _=>.skip
def afterMaterialize : ProgHOL 64 := match materializeCall with | .decCall _ _ _ _ rest=>rest | _=>.skip
def materializeArguments : List (ExpHOL 64) := [localVar "db",.rfield 1 (localVar "r"),.rfield 2 (localVar "r")]

set_option maxRecDepth 100000 in
/-- Current239's real missing-node guard and unchanged materializer call. -/
theorem lookup_tail_shape : afterLookup=.seq missingGuard materializeCall ∧
    materializeCall=.decCall (ofString "nd") .one (ofString "_decode_witness_node") materializeArguments afterMaterialize := by
  simp only [afterLookup,lookupCall,afterCompare,body,Guest.Software.guestFn_decode_witness_to_mpt,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    missingGuard,missingTest,missingCall,materializeCall,materializeArguments,afterMaterialize,localVar]
  trivial

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.lookup_tail_shape
