import InitECandidate.Solver.Input.AllocationControl
import InitECandidate.Solver.Input.InitializerControl

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

/-- Full readonly metadata/FFI retention from an actual optional allocation's
control contract. The real heap/global update is erased only in this frame. -/
theorem allocation_context (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (array amount : BitVec 64)
    (empty : Prop) [Decidable empty]
    (control : BackingLayout.control target=BackingLayout.control (if empty then source else PersistentAlloc.post source array amount)) :
    InitializerAllocations.context target=InitializerAllocations.context source := by
  by_cases h : empty
  · simp only [if_pos h] at control
    have projected := congrArg InitializerAllocations.context control
    exact projected
  · simp only [if_neg h] at control
    have projected := congrArg InitializerAllocations.context control
    exact projected

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.allocation_context
