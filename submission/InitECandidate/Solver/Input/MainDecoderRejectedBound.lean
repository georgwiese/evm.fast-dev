import InitECandidate.Solver.Input.MainErrorEntry
import InitECandidate.Solver.Input.MainErrorStopped
import InitECandidate.Solver.Input.MainDecoderRejectClock

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

private theorem decoder_sequence : DecoderSetup.decoder = .seq program continuation := by
  rw [program_shape]
  exact original_shape

/-- Complete actual decoder/catch-handler suffix for all three early
rejections. The success continuation is never entered, on any outcome. -/
theorem rejected_cost (input : Guest.InputBlob) (before source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (copied : InputCopied input before source) (bounded : input.length % 2 ^ 64 ≤ Guest.maxInputBytes) (rejects : Rejects input) :
    (DecoderSetup.entered source input).clock - (evaluateHOLFiniteState (DecoderSetup.entered source input) DecoderSetup.decoder).2.clock ≤ 53 := by
  let caller := DecoderSetup.entered source input
  by_cases enough : 2 ≤ caller.clock
  · have first := reject_to_handler input before source copied bounded rejects enough
    have cost := ErrorHandler.early_cost input before source copied bounded
    have clock := evaluateHOLFiniteState_clock_le (handlerState source input) handler
    have stopped := ErrorHandler.stopped (handlerState source input)
    rw [decoder_sequence,evaluateHOLFiniteState_seq_line780,first]
    generalize actual : evaluateHOLFiniteState (handlerState source input) handler = output at cost clock stopped ⊢
    obtain ⟨result,target⟩ := output
    cases result with
    | none => exact False.elim (stopped rfl)
    | some result =>
      change caller.clock - target.clock ≤ 53
      change caller.clock - 2 - target.clock ≤ 51 at cost
      change target.clock ≤ caller.clock - 2 at clock
      omega
  · have short : caller.clock < 2 := by omega
    have timed := rejected_short_timeout input before source copied bounded rejects short
    have first : evaluateHOLFiniteState caller program = (some .timeOut,(evaluateHOLFiniteState caller program).2) := Prod.ext timed rfl
    rw [decoder_sequence,evaluateHOLFiniteState_seq_line780,first]
    change caller.clock - (evaluateHOLFiniteState caller program).2.clock ≤ 53
    omega

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.rejected_cost
