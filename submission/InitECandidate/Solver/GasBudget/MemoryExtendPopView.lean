import InitECandidate.Solver.GasBudget.MemoryBufferOwnership
import InitECandidate.Solver.GasBudget.PrefixEnvironment

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack PanSemStateFiniteExact

theorem View.after_pops {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame base length capacity pointer scratch : BitVec 64} {paid : Nat}
    (view : View source frame base length capacity pointer scratch)
    (effect : StackPop.PrefixEffect source target frame paid) : View target frame base length capacity pointer scratch := by
  have current := view.with_memory target.memory
    ((effect.outside _ (offsets_ne frame 24#64 16#64 (by decide))).trans view.baseCell)
    ((effect.outside _ (offsets_ne frame 32#64 16#64 (by decide))).trans view.lengthCell)
    ((effect.outside _ (offsets_ne frame 40#64 16#64 (by decide))).trans view.capacityCell)
  apply current.after_erase
  have fields := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with clock := 0}) effect.fields
  exact fields

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.View.after_pops
