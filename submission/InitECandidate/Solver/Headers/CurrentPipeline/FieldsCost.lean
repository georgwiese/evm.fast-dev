import InitECandidate.Solver.Headers.CurrentPipeline.Cost

namespace InitECandidate.Solver.Headers.CurrentPipeline
open Pipeline
open Flapjack PanSemStateFiniteExact

/-- Complete literal current header-field extraction, on every outcome.
Each selected encoded row is decoded at most twice; real typed stores and
all helper/caller overheads are included. Straight-line target work is separate. -/
theorem fields_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header current : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem)
    (state : State source pointer array header current bytes items []) :
    source.clock-(evaluateHOLFiniteState source Decode.afterAllocation).2.clock≤120*bytes+455 := by
  rw [original_fields]
  have paid:=cost source pointer array header current bytes items [] fields state (fields_valid current items.length state.branch)
  have count : items.length≤23 := by rcases state.branch with branch|branch <;> omega
  exact Nat.le_trans paid (price_bytes source pointer bytes items current state.slices.itemsAtInput count)

end InitECandidate.Solver.Headers.CurrentPipeline

#print axioms InitECandidate.Solver.Headers.CurrentPipeline.fields_cost
