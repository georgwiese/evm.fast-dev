import InitECandidate.Solver.GasBudget.MemoryExtendPopView

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack PanSemStateFiniteExact

/-- Ledger-only writes protect every owned buffer header. The actual gas
operation supplies the canonical state and outside-word frame at each use. -/
theorem View.after_ledger {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame base length capacity pointer scratch : BitVec 64}
    (view : View source frame base length capacity pointer scratch)
    (fields : emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := target.memory, clock := target.clock})
    (outside : ∀ address, address ≠ frame + 64#64 → address ≠ frame + 184#64 → target.memory address = source.memory address) :
    View target frame base length capacity pointer scratch := by
  have current := view.with_memory target.memory
    ((outside _ (offsets_ne frame 24#64 64#64 (by decide)) (offsets_ne frame 24#64 184#64 (by decide))).trans view.baseCell)
    ((outside _ (offsets_ne frame 32#64 64#64 (by decide)) (offsets_ne frame 32#64 184#64 (by decide))).trans view.lengthCell)
    ((outside _ (offsets_ne frame 40#64 64#64 (by decide)) (offsets_ne frame 40#64 184#64 (by decide))).trans view.capacityCell)
  apply current.after_erase
  have erased := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with clock := 0}) fields
  exact erased

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.View.after_ledger
