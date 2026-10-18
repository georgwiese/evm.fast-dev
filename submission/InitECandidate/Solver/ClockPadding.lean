import InitECandidate.Solver.ClockStutter

namespace InitECandidate.Solver
open Flapjack PanSemStateFiniteExact

/-- Remove the same added clock from both ends of a bounded execution.
The funding premise also covers extra=0, when truncated subtraction alone
would not exclude an overdrawn claimed price. Nonlocal fields are arbitrary. -/
theorem strip_clock_padding {F : Type} (source target model : PanSemStateFiniteExact 64 F) (paid extra : Nat)
    (funded : paid ≤ source.clock + extra)
    (frame : emptyLocalsHOLFinite {target with clock := target.clock + extra} =
      emptyLocalsHOLFinite {model with clock := source.clock + extra - paid}) :
    paid ≤ source.clock ∧ emptyLocalsHOLFinite target = emptyLocalsHOLFinite {model with clock := source.clock - paid} := by
  have sameClock := congrArg (fun state : PanSemStateFiniteExact 64 F => state.clock) frame
  change target.clock + extra = source.clock + extra - paid at sameClock
  have fits : paid ≤ source.clock := by omega
  have spent : target.clock = source.clock - paid := by omega
  have reset := congrArg (fun state : PanSemStateFiniteExact 64 F => {state with clock := target.clock}) frame
  change emptyLocalsHOLFinite target = emptyLocalsHOLFinite {model with clock := target.clock} at reset
  rw [spent] at reset
  exact ⟨fits, reset⟩

end InitECandidate.Solver

#print axioms InitECandidate.Solver.strip_clock_padding
