import InitECandidate.Solver.GasBudget.FramePrefixEffect
import InitECandidate.Solver.GasBudget.FrameChargeEvent

namespace InitECandidate.Solver.GasBudget
open Flapjack PanSemStateFiniteExact

theorem FrameChargeEvent.prepend {source middle ready : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame : BitVec 64} {first paid amount : Nat}
    (event : FrameChargeEvent middle ready frame paid amount) (before : FramePrefixEffect source middle frame first) :
    FrameChargeEvent source ready frame (first + paid) amount := by
  have lift := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    emptyLocalsHOLFinite {state with memory := ready.memory, clock := ready.clock}) before.fields
  refine ⟨?_, by rw [event.clock, before.clock]; omega, event.fields.trans lift, event.budget.trans before.budget, ?_, event.positive, ?_⟩
  · have fits := event.fits
    have prior := before.fits
    rw [before.clock] at fits
    omega
  · rw [event.credit]
    simp only [wordAt, before.used]
  · intro query notSP notGas notUsed away
    exact (event.outside query notSP notGas notUsed away).trans (before.outside query notSP away)

end InitECandidate.Solver.GasBudget

#print axioms InitECandidate.Solver.GasBudget.FrameChargeEvent.prepend
