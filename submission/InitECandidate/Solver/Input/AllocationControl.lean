import InitECandidate.Solver.Input.PayloadWordStore

namespace InitECandidate.Solver.Input
open Flapjack PanSemStateFiniteExact

/-- Allocation may change the heap global, never the code, exception shapes or
ordinary address domain. This interface avoids expanding a conditional state. -/
theorem allocation_control_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (array amount : BitVec 64)
    (empty : Prop) [Decidable empty]
    (frame : WitnessRadix.BackingLayout.control target=WitnessRadix.BackingLayout.control
      (if empty then source else WitnessRadix.PersistentAlloc.post source array amount)) :
    target.memaddrs=source.memaddrs ∧ target.code=source.code ∧ target.eshapes=source.eshapes := by
  by_cases zero : empty
  · rw [if_pos zero] at frame
    have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
    have code:=congrArg PanSemStateFiniteExact.code frame
    have shapes:=congrArg PanSemStateFiniteExact.eshapes frame
    exact ⟨domain,code,shapes⟩
  · rw [if_neg zero] at frame
    have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
    have code:=congrArg PanSemStateFiniteExact.code frame
    have shapes:=congrArg PanSemStateFiniteExact.eshapes frame
    exact ⟨domain,code,shapes⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.allocation_control_fields
