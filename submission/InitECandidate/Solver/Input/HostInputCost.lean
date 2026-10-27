import InitECandidate.Solver.Input.HostInputCode
import InitECandidate.Solver.Input.QuietClockShared
import InitECandidate.Solver.Input.ClockCostScoped

namespace InitECandidate.Solver.Input.HostPrecheck
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem Byte.body_cost (code) : ClockCost.Bound code Byte.body 0 := by
  rw [Byte.body_shape]
  exact ClockCost.declared code _ _ _ _ 0 (ClockCost.sequence code _ _ 0 0
    (ClockCost.shared_load code _ _ _ _) (ClockCost.returned code _))

theorem Le32.body_cost (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code Le32.body 4 := by
  have entry := byte_installed code installed
  have last : ClockCost.Bound code Le32.afterB2 1 :=
    ClockCost.scoped_body code _ _ _ _ _ Byte.formals Byte.body .one 0 0 entry
      (Byte.body_cost code) (ClockCost.returned code Le32.value)
  have second : ClockCost.Bound code Le32.afterB1 2 :=
    ClockCost.scoped_body code _ _ _ _ _ Byte.formals Byte.body .one 0 1 entry
      (Byte.body_cost code) last
  have first : ClockCost.Bound code Le32.afterB0 3 :=
    ClockCost.scoped_body code _ _ _ _ _ Byte.formals Byte.body .one 0 2 entry
      (Byte.body_cost code) second
  rw [Le32.body_shape]
  exact ClockCost.scoped_body code _ _ _ _ _ Byte.formals Byte.body .one 0 3 entry
    (Byte.body_cost code) first

theorem byte_call_cost (code) (installed : OriginalCode.Installed code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination) (ofString "host_input_byte") arguments) 1 :=
  ClockCost.call_body code destination _ arguments Byte.formals Byte.body .one 0
    (byte_installed code installed) (Byte.body_cost code)

theorem le32_call_cost (code) (installed : OriginalCode.Installed code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination) (ofString "host_input_le32") arguments) 5 :=
  ClockCost.call_body code destination _ arguments Le32.formals Le32.body .one 4
    (le32_installed code installed) (Le32.body_cost code installed)

end InitECandidate.Solver.Input.HostPrecheck

#print axioms InitECandidate.Solver.Input.HostPrecheck.Byte.body_cost
#print axioms InitECandidate.Solver.Input.HostPrecheck.Le32.body_cost
#print axioms InitECandidate.Solver.Input.HostPrecheck.byte_call_cost
#print axioms InitECandidate.Solver.Input.HostPrecheck.le32_call_cost
