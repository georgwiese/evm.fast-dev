import InitECandidate.Solver.Input.CurrentU256.Program
import InitECandidate.Solver.Input.CurrentU256.Swap
import InitECandidate.Solver.Input.LocalEffectsLoop
import InitECandidate.Solver.Input.LocalEffectsScoped

namespace InitECandidate.Solver.Input.CurrentU256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem slow_readonly (code) : LocalEffects.Preserves code slow := by
  simp only [slow,zeros,loop,loopBody,branches,choice,increment]
  repeat first
    | apply LocalEffects.declared
    | apply LocalEffects.sequence
    | apply LocalEffects.loop
    | apply LocalEffects.conditional
    | exact LocalEffects.assign code _ _
    | exact LocalEffects.returned code _
    | exact LocalEffects.skip code

set_option maxRecDepth 10000 in
theorem fast_readonly (code) (installed : OriginalCode.Installed code) : LocalEffects.Preserves code fast := by
  simp only [fast,body,Guest.Software.guestFn_u256_from_be,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat first
    | apply LocalEffects.declared
    | apply LocalEffects.sequence
    | exact LocalEffects.assign code _ _
    | exact LocalEffects.returned code _
    | apply LocalEffects.scoped_body code _ _ (ofString "bswap64") _ _ _ swapBody .one (swap_original_code code installed) (swap_readonly code)

/-- Both actual conversion branches only read memory and change locals,
including failures and exhausted clocks. -/
theorem readonly (code) (installed : OriginalCode.Installed code) : LocalEffects.Preserves code body := by
  rw [body_shape]
  exact LocalEffects.sequence code _ slow
    (LocalEffects.conditional code fastTest fast .skip (fast_readonly code installed) (LocalEffects.skip code)) (slow_readonly code)

end InitECandidate.Solver.Input.CurrentU256

#print axioms InitECandidate.Solver.Input.CurrentU256.slow_readonly
#print axioms InitECandidate.Solver.Input.CurrentU256.fast_readonly
#print axioms InitECandidate.Solver.Input.CurrentU256.readonly
