import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.QuietClock
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Input.CurrentU256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def swapBody : ProgHOL 64 := match Guest.Software.guestFn_bswap64 with | .function fn=>progToHOL fn.body | _=>.skip

theorem swap_original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "bswap64")=some ([(ofString "x",.one)],swapBody,.one) := by
  have checked:=OriginalCode.indexed code installed 18 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_bswap64) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,swapBody,
    Guest.Software.guestFn_bswap64,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- Actual byte swapping spends no source call/loop clock and only changes
locals; its straight-line target instructions still need target pricing. -/
theorem swap_quiet (code) : QuietClock.Preserves code swapBody := by
  simp only [swapBody,Guest.Software.guestFn_bswap64,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  apply QuietClock.sequence
  · exact QuietClock.assign code _ _
  · apply QuietClock.sequence
    · exact QuietClock.assign code _ _
    · exact QuietClock.returned code _

theorem swap_readonly (code) : LocalEffects.Preserves code swapBody := by
  simp only [swapBody,Guest.Software.guestFn_bswap64,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  apply LocalEffects.sequence
  · exact LocalEffects.assign code _ _
  · apply LocalEffects.sequence
    · exact LocalEffects.assign code _ _
    · exact LocalEffects.returned code _

end InitECandidate.Solver.Input.CurrentU256

#print axioms InitECandidate.Solver.Input.CurrentU256.swap_original_code
#print axioms InitECandidate.Solver.Input.CurrentU256.swap_quiet
#print axioms InitECandidate.Solver.Input.CurrentU256.swap_readonly
