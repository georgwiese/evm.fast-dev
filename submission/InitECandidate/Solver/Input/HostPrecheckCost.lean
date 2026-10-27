import InitECandidate.Solver.Input.HostInputCost
import InitECandidate.Solver.Input.OffsetsFixedCountCall

-- Generated from the actual software precheck by generate-host-precheck-cost.py.
-- The candidate price is justified only by a successful Lean build of this file.
namespace InitECandidate.Solver.Input.HostPrecheck
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString GasBudget.OriginalCodeEnvironment

def body : ProgHOL 64 := match Guest.Software.guestFn_precheck_host_ssz_header with
  | .function fn => progToHOL fn.body | _ => .skip

set_option maxRecDepth 100000 in
theorem precheck_installed (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "precheck_host_ssz_header") = some ([], body, .one) := by
  have found := OriginalCode.indexed code installed 182
    (originalEntry Guest.Software.guestFn_precheck_host_ssz_header) (by rfl)
  simpa only [originalEntry, declToHOL, funDeclToHOL, body,
    Guest.Software.guestFn_precheck_host_ssz_header, shapeToHOL, List.map_nil] using found

set_option maxRecDepth 100000 in
/-- All actual precheck outcomes, including failed host reads, failed stores
and decoder exceptions. This counts source call/loop ticks, not target steps. -/
theorem body_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code body 85 := by
  simp only [body, Guest.Software.guestFn_precheck_host_ssz_header, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  exact (ClockCost.declared code _ _ _ _ 85
  (ClockCost.sequence code _ _ 0 85
  (ClockCost.shared_load code _ _ _ _)
  (ClockCost.sequence code _ _ 0 85
  (ClockCost.conditional code _ _ _ 0 0
  (ClockCost.returned code _)
  (ClockCost.skip code))
  (ClockCost.sequence code _ _ 1 84
  (ClockCost.conditional code _ _ _ 1 0
  (ClockCost.call_body code (some none) _ _ SszFail.formals SszFail.body .one 0
  (SszCurrentCode.fail_installed code installed) (Offsets.failure_body_cost code))
  (ClockCost.skip code))
  (ClockCost.scoped_body code _ _ _ _ _ Byte.formals Byte.body .one 0 83
  (byte_installed code installed) (Byte.body_cost code)
  (ClockCost.scoped_body code _ _ _ _ _ Byte.formals Byte.body .one 0 82
  (byte_installed code installed) (Byte.body_cost code)
  (ClockCost.sequence code _ _ 1 81
  (ClockCost.conditional code _ _ _ 1 0
  (ClockCost.call_body code (some none) _ _ SszFail.formals SszFail.body .one 0
  (SszCurrentCode.fail_installed code installed) (Offsets.failure_body_cost code))
  (ClockCost.skip code))
  (ClockCost.declared code _ _ _ _ 81
  (ClockCost.sequence code _ _ 1 80
  (ClockCost.conditional code _ _ _ 1 0
  (ClockCost.call_body code (some none) _ _ SszFail.formals SszFail.body .one 0
  (SszCurrentCode.fail_installed code installed) (Offsets.failure_body_cost code))
  (ClockCost.skip code))
  (ClockCost.scoped_body code _ _ _ _ _ Le32.formals Le32.body .one 4 75
  (le32_installed code installed) (Le32.body_cost code installed)
  (ClockCost.scoped_body code _ _ _ _ _ Le32.formals Le32.body .one 4 70
  (le32_installed code installed) (Le32.body_cost code installed)
  (ClockCost.sequence code _ _ 0 70
  (ClockCost.store code _ _)
  (ClockCost.sequence code _ _ 0 70
  (ClockCost.store code _ _)
  (ClockCost.sequence code _ _ 8 62
  (Offsets.call_fixed_count_cost code installed 2 (by decide) _ _ _)
  (ClockCost.declared code _ _ _ _ 62
  (ClockCost.sequence code _ _ 1 61
  (ClockCost.conditional code _ _ _ 1 0
  (ClockCost.call_body code (some none) _ _ SszFail.formals SszFail.body .one 0
  (SszCurrentCode.fail_installed code installed) (Offsets.failure_body_cost code))
  (ClockCost.skip code))
  (ClockCost.declared code _ _ _ _ 61
  (ClockCost.scoped_body code _ _ _ _ _ Le32.formals Le32.body .one 4 56
  (le32_installed code installed) (Le32.body_cost code installed)
  (ClockCost.scoped_body code _ _ _ _ _ Le32.formals Le32.body .one 4 51
  (le32_installed code installed) (Le32.body_cost code installed)
  (ClockCost.scoped_body code _ _ _ _ _ Le32.formals Le32.body .one 4 46
  (le32_installed code installed) (Le32.body_cost code installed)
  (ClockCost.sequence code _ _ 0 46
  (ClockCost.store code _ _)
  (ClockCost.sequence code _ _ 0 46
  (ClockCost.store code _ _)
  (ClockCost.sequence code _ _ 0 46
  (ClockCost.store code _ _)
  (ClockCost.sequence code _ _ 11 35
  (Offsets.call_fixed_count_cost code installed 3 (by decide) _ _ _)
  (ClockCost.declared code _ _ _ _ 35
  (ClockCost.sequence code _ _ 1 34
  (ClockCost.conditional code _ _ _ 1 0
  (ClockCost.call_body code (some none) _ _ SszFail.formals SszFail.body .one 0
  (SszCurrentCode.fail_installed code installed) (Offsets.failure_body_cost code))
  (ClockCost.skip code))
  (ClockCost.declared code _ _ _ _ 34
  (ClockCost.scoped_body code _ _ _ _ _ Le32.formals Le32.body .one 4 29
  (le32_installed code installed) (Le32.body_cost code installed)
  (ClockCost.scoped_body code _ _ _ _ _ Le32.formals Le32.body .one 4 24
  (le32_installed code installed) (Le32.body_cost code installed)
  (ClockCost.scoped_body code _ _ _ _ _ Le32.formals Le32.body .one 4 19
  (le32_installed code installed) (Le32.body_cost code installed)
  (ClockCost.scoped_body code _ _ _ _ _ Le32.formals Le32.body .one 4 14
  (le32_installed code installed) (Le32.body_cost code installed)
  (ClockCost.sequence code _ _ 0 14
  (ClockCost.store code _ _)
  (ClockCost.sequence code _ _ 0 14
  (ClockCost.store code _ _)
  (ClockCost.sequence code _ _ 0 14
  (ClockCost.store code _ _)
  (ClockCost.sequence code _ _ 0 14
  (ClockCost.store code _ _)
  (ClockCost.sequence code _ _ 14 0
  (Offsets.call_fixed_count_cost code installed 4 (by decide) _ _ _)
  (ClockCost.returned code _)))))))))))))))))))))))))))))))))))))

theorem call_cost (code) (installed : OriginalCode.Installed code)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    ClockCost.Bound code (.call (LocalEffects.callInfo destination)
      (ofString "precheck_host_ssz_header") arguments) 86 :=
  ClockCost.call_body code destination _ arguments [] body .one 85
    (precheck_installed code installed) (body_cost code installed)

end InitECandidate.Solver.Input.HostPrecheck

#print axioms InitECandidate.Solver.Input.HostPrecheck.precheck_installed
#print axioms InitECandidate.Solver.Input.HostPrecheck.body_cost
#print axioms InitECandidate.Solver.Input.HostPrecheck.call_cost
