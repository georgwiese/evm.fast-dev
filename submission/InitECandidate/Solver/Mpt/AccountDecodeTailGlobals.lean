import InitECandidate.Solver.Mpt.AccountDecodeTailCost
import InitECandidate.Solver.Input.BufferGlobals
import InitECandidate.Solver.Input.LocalEffectsLoop

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

theorem nonce_loop_readonly (code) : Input.LocalEffects.Preserves code nonceLoop := by
  rw [nonce_loop_shape,nonce_body_shape]
  unfold nonceAccumulate increment
  exact Input.LocalEffects.loop code _ _
    (Input.LocalEffects.sequence code _ _ (Input.LocalEffects.assign code _ _) (Input.LocalEffects.assign code _ _))

set_option maxRecDepth 10000 in
/-- Every post-field decoder outcome preserves all globals. Its only helper
is the original memory clear; guards may stop at original mpt_fail. -/
theorem after_fields_globals (key : MlS) (code) (installed : Input.OriginalCode.Installed code) :
    Input.GlobalEffects.Preserves key code afterFields := by
  rw [after_fields_shape,nonce_loop_shape,nonce_body_shape,after_nonce_shape,balance_phase_shape,balance_loop_shape,balance_body_shape,after_balance_shape]
  unfold nonceAccumulate increment balanceStore fail
  repeat first
    | apply Input.GlobalEffects.declared
    | apply Input.GlobalEffects.sequence
    | apply Input.GlobalEffects.conditional
    | apply Input.GlobalEffects.loop
    | exact Input.GlobalEffects.assign key code _ _
    | exact Input.GlobalEffects.store key code _ _
    | exact Input.GlobalEffects.returned key code _
    | exact Input.GlobalEffects.skip key code
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "mpt_fail") _ Fail.formals Fail.body .one
        (Fail.original_code code installed) (Input.GlobalEffects.of_readonly key code _ (Fail.readonly code))
    | exact Input.GlobalEffects.call_body key code (some none) (ofString "memzero") _ Zero.formals Zero.body .one
        (Zero.original_code code installed) (Zero.globals key code)

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.nonce_loop_readonly
#print axioms InitECandidate.Solver.Mpt.AccountDecode.after_fields_globals
