import InitECandidate.Solver.Input.CeilLog2Call
import InitECandidate.Solver.Input.UnsignedMaxCall
import InitECandidate.Solver.Input.ShaPairCallCost

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
set_option maxRecDepth 100000

def body : ProgHOL 64 := match Guest.guestFn_merkleize with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "p",.one),(ofString "n",.one),(ofString "limit",.one),(ofString "out",.one)]
def afterLimit : ProgHOL 64 := match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterCount : ProgHOL 64 := match afterLimit with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterDepth : ProgHOL 64 := match afterCount with | .decCall _ _ _ _ rest=>rest | _=>.skip

theorem prefix_shape : body=.decCall (ofString "dl") .one (ofString "ceil_log2") [localVar "limit"] afterLimit ∧
    afterLimit=.decCall (ofString "dn") .one (ofString "ceil_log2") [localVar "n"] afterCount ∧
    afterCount=.decCall (ofString "target") .one (ofString "max") [localVar "dl",localVar "dn"] afterDepth := by
  simp only [body,afterLimit,afterCount,afterDepth,Guest.guestFn_merkleize,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
  exact ⟨True.intro,True.intro,True.intro⟩

theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "merkleize")=some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 175 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_merkleize) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_merkleize,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.prefix_shape
#print axioms InitECandidate.Solver.Input.Merkle.original_code
