import InitECandidate.Solver.Mpt.DeleteBodyProgram
import InitECandidate.Solver.MutableTable.MemeqAnyCall

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def leafLengthChoice : ProgHOL 64:=match leafBlock with | .seq _ rest=>rest | _=>.skip
def leafCompare : ProgHOL 64:=match leafLengthChoice with | .ite _ first _=>first | _=>.skip
def leafCompared : ProgHOL 64:=match leafCompare with | .decCall _ _ _ _ rest=>rest | _=>.skip
def leafCompareArguments : List (ExpHOL 64):=[field "node" 32#64,keySuffix,remaining]

theorem leaf_shapes : leafBlock=.seq (.assign .local (ofString "res") (localVar "node")) leafLengthChoice ∧
    leafLengthChoice=.ite (.cmp .equal (field "node" 40#64) remaining) leafCompare .skip ∧
    leafCompare=.decCall (ofString "eq") .one (ofString "memeq") leafCompareArguments leafCompared ∧
    leafCompared=.ite (.cmp .notEqual (localVar "eq") (.const 0#64)) (.assign .local (ofString "res") (.const 0#64)) .skip := by
  simp only [leafLengthChoice,leafCompare,leafCompared,leaf_shape,leafCompareArguments]
  simp

/-- Comparisons and scalar result choices preserve every nonlocal
field on all outcomes, including failed reads and timeouts. -/
theorem leaf_readonly (code) (installed : Input.OriginalCode.Installed code) : Input.LocalEffects.Preserves code leafBlock := by
  rw [leaf_shapes.1,leaf_shapes.2.1,leaf_shapes.2.2.1,leaf_shapes.2.2.2]
  repeat first
    | apply Input.LocalEffects.sequence
    | apply Input.LocalEffects.conditional
    | exact Input.LocalEffects.assign code _ _
    | exact Input.LocalEffects.skip code
    | apply Input.LocalEffects.scoped_body code (ofString "eq") .one (ofString "memeq") _ _ Memeq32.formals Memeq32.body .one
        (MutableTable.MemeqAny.original_code code installed) (MutableTable.MemeqAny.readonly code)

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.leaf_shapes
#print axioms InitECandidate.Solver.Mpt.DeleteBody.leaf_readonly
