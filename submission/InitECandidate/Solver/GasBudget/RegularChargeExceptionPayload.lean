import InitECandidate.Solver.GasBudget.RegularCharge
import InitECandidate.Solver.Input.NoExceptionEvent

namespace InitECandidate.Solver.GasBudget.RegularCharge
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The unchanged charging body can only raise its literal EvmErr4, even
when current reads fail or the caller clock is insufficient. -/
theorem excludes_other_payload (code) (payload : ValueHOL 64) (other : payload ≠ .val (.word 4#64)) :
    Input.NoExceptionEvent.Safe code (ofString "EvmErr") payload body := by
  simp only [body, Guest.guestFn_charge_gas, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil]
  repeat first
    | apply Input.NoExceptionEvent.declared
    | apply Input.NoExceptionEvent.sequence
    | apply Input.NoExceptionEvent.conditional
    | exact Input.NoExceptionEvent.of_all code _ _ _ (Input.NoException.skip code)
    | exact Input.NoExceptionEvent.of_all code _ _ _ (Input.NoException.store code _ _)
    | exact Input.NoExceptionEvent.of_all code _ _ _ (Input.NoException.returned code _)
    | exact Input.NoExceptionEvent.raise_literal code _ _ payload 4#64 (Ne.symm other)

end InitECandidate.Solver.GasBudget.RegularCharge

#print axioms InitECandidate.Solver.GasBudget.RegularCharge.excludes_other_payload
