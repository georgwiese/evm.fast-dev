import InitECandidate.Solver.GasBudget.StackPopCallException
import InitECandidate.Solver.Input.NoExceptionEvent

namespace InitECandidate.Solver.GasBudget.StackPop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem excludes_other_payload (code) (payload : ValueHOL 64) (other : payload ≠ .val (.word 2#64)) :
    Input.NoExceptionEvent.Safe code (ofString "EvmErr") payload body := by
  simp only [body, Guest.guestFn_stack_pop, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil]
  repeat first
    | apply Input.NoExceptionEvent.declared
    | apply Input.NoExceptionEvent.sequence
    | apply Input.NoExceptionEvent.conditional
    | exact Input.NoExceptionEvent.of_all code _ _ _ (Input.NoException.skip code)
    | exact Input.NoExceptionEvent.of_all code _ _ _ (Input.NoException.store code _ _)
    | exact Input.NoExceptionEvent.of_all code _ _ _ (Input.NoException.assign code _ _)
    | exact Input.NoExceptionEvent.of_all code _ _ _ (Input.NoException.returned code _)
    | exact Input.NoExceptionEvent.raise_literal code _ _ payload 2#64 (Ne.symm other)

end InitECandidate.Solver.GasBudget.StackPop

#print axioms InitECandidate.Solver.GasBudget.StackPop.excludes_other_payload
