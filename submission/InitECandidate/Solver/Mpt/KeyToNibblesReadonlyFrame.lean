import InitECandidate.Solver.Mpt.KeyToNibblesFootprint
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack PanSemStateFiniteExact

theorem OutputFrame.of_readonly (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (out : BitVec 64)
    (same : Input.LocalEffects.erase post=Input.LocalEffects.erase source) : OutputFrame source post out := by
  have fields := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with memory := fun _ => .word 0#64}) same
  have memory := Input.LocalEffects.memory_of_erase source post same
  exact ⟨fields,fun query outside => congrFun memory query⟩

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.OutputFrame.of_readonly
