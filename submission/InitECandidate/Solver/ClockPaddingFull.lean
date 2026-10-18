import InitECandidate.Solver.ClockPadding

namespace InitECandidate.Solver
open Flapjack PanSemStateFiniteExact

/-- Remove temporary clock padding from a complete caller state. This also
retains its actual caller locals, unlike a callee's empty-locals frame. -/
theorem strip_full_clock_padding {F : Type} (source target model : PanSemStateFiniteExact 64 F) (paid extra : Nat)
    (funded : paid ≤ source.clock + extra)
    (frame : {target with clock := target.clock + extra} = {model with clock := source.clock + extra - paid}) :
    paid ≤ source.clock ∧ target = {model with clock := source.clock - paid} := by
  have clock := congrArg PanSemStateFiniteExact.clock frame
  change target.clock + extra = source.clock + extra - paid at clock
  have fits : paid ≤ source.clock := by omega
  have spent : target.clock = source.clock - paid := by omega
  have reset := congrArg (fun state : PanSemStateFiniteExact 64 F => {state with clock := target.clock}) frame
  change target = {model with clock := target.clock} at reset
  rw [spent] at reset
  exact ⟨fits, reset⟩

end InitECandidate.Solver

#print axioms InitECandidate.Solver.strip_full_clock_padding
