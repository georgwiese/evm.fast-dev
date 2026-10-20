import InitECandidate.Solver.Input.MainDecoderReject
import InitECandidate.Solver.Input.ClockExhaustion

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem Environment.clocked (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment input source) (clock : Nat) : Environment input {source with clock := clock} :=
  ⟨environment.pointer,environment.length,environment.bytes,environment.offsets,environment.heap,environment.scalars,environment.code,
    environment.shapes,environment.domain,environment.shared,environment.little,environment.oracle,environment.host⟩

theorem rejected_zero_timeout (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment input source) (rejects : Rejects input) (zero : source.clock = 0) :
    (evaluateHOLFiniteState source Header.body).1 = some .timeOut := by
  have padded := rejected_body input {source with clock := source.clock + 1} (environment.clocked input source (source.clock + 1)) rejects (by simp)
  exact timeout_of_padded_remainder source _ Header.body 1 _ padded (by change source.clock + 1 - 1 < 1; omega)

/-- On a real rejected input fewer than two caller ticks necessarily time
out before the handler. This derives funding from the current execution. -/
theorem rejected_short_timeout (input : Guest.InputBlob) (before source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (copied : InputCopied input before source) (bounded : input.length % 2 ^ 64 ≤ Guest.maxInputBytes)
    (rejects : Rejects input) (short : (DecoderSetup.entered source input).clock < 2) :
    (evaluateHOLFiniteState (DecoderSetup.entered source input) program).1 = some .timeOut := by
  obtain ⟨callee,args,called,environment⟩ := entry_data input before source copied bounded
  let caller := DecoderSetup.entered source input
  have callerShort : caller.clock < 2 := short
  rw [program_shape,evaluateHOLFiniteState_call,args]
  simp only [called]
  dsimp only [caller] at callerShort ⊢
  by_cases zero : (DecoderSetup.entered source input).clock = 0
  · simp only [if_pos zero]
  · simp only [if_neg zero]
    have clockOne : caller.clock = 1 := by change (DecoderSetup.entered source input).clock = 1; omega
    let entry := callEntryStateHOLFinite caller callee
    have timed := rejected_zero_timeout input entry environment rejects (by change caller.clock - 1 = 0; rw [clockOne])
    have actual : evaluateHOLFiniteState entry Header.body = (some .timeOut,(evaluateHOLFiniteState entry Header.body).2) := Prod.ext timed rfl
    rw [actual]

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.Environment.clocked
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.rejected_zero_timeout
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.rejected_short_timeout
