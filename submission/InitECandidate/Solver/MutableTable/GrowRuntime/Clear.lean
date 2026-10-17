import InitECandidate.Solver.MutableTable.GrowProgram
import InitECandidate.Solver.MutableTable.GrowRuntime.Memory

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def clearCall : ProgHOL 64 := .call (some (none, none)) (ofString "memzero") [localVar "nused", localVar "ncap"]
def clearState {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : Plan) :=
  {source with memory := (Zero.finalMemory source.memory (cell plan .used 0) plan.capacity), clock := source.clock - (Zero.price plan.capacity + 1)}

/-- The actual growth clear call. All byte mappings, alignment and no-wrap
premises are derived from the new table's physical ownership. -/
theorem clear_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (multiple : plan.capacity % 8 = 0)
    (usedLocal : source.locals.lookup (ofString "nused") = some (.val (.word (cell plan .used 0))))
    (capLocal : source.locals.lookup (ofString "ncap") = some (.val (.word (BitVec.ofNat 64 plan.capacity))))
    (code : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (enough : Zero.price plan.capacity + 1 ≤ source.clock) :
    evaluateHOLFiniteState source clearCall = (none, clearState source plan) := by
  have high := valid.upper .used
  change plan.base .used + rounded plan.capacity ≤ 33806089496 at high
  have roundHigh := (rounded_bounds plan.capacity).1
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
      [localVar "nused", localVar "ncap"] = some (Zero.values (cell plan .used 0) plan.capacity) := by
    simp [Zero.values, localVar, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, usedLocal, capLocal]
  apply Zero.call_execute source _ _ _ args code (by omega) multiple
  · rw [base_number kind plan valid .used]
    exact valid.aligned .used
  · intro offset inside aligned
    rw [domain]
    change InitE.ordinaryDomain (cell plan .used 0 + BitVec.ofNat 64 offset)
    rw [constant_cell]
    exact mapped kind plan valid .used offset (by change offset < rounded plan.capacity; omega) aligned
  · exact enough

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.clear_execute
