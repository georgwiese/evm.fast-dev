import InitECandidate.Solver.Input.MainRequestFields
import InitECandidate.Solver.Input.RequestPrefixEntry
import InitECandidate.Solver.Input.SszGuardTrace

namespace InitECandidate.Solver.Input.Main.RequestPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The original request-length guard either stops with its actual SszErr81
or resumes the original request body. Funding comes from the actual enclosing
run, and the nlen word was derived by the real prefix declarations. -/
theorem length_trace (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (clock : Nat)
    (environment : DecoderCall.Environment input source)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState (ready source input clock) (.seq Request.lengthGuard Request.requestBody) = (result,post))
    (notTimeout : result ≠ some .timeOut) :
    (Guest.GasLimit.le32 input 6 - 16 < 44 ∧ 1 ≤ (ready source input clock).clock ∧
      result = some (.exception (ofString "SszErr") (.val (.word 81#64))) ∧ post = emptyLocalsHOLFinite {ready source input clock with clock := (ready source input clock).clock - 1}) ∨
    (44 ≤ Guest.GasLimit.le32 input 6 - 16 ∧ evaluateHOLFiniteState (ready source input clock) Request.requestBody = (result,post)) := by
  have small : Guest.GasLimit.le32 input 6 - 16 < 2^64 := by
    have bound := HostGas.le32_lt input 6
    rw [HostGas.le32_eq input 6 (by decide)] at bound
    omega
  have test := Request.length_test_read (ready source input clock) (Guest.GasLimit.le32 input 6 - 16) small (ready_bindings source input clock).2
  have outcome := Header.guard_trace (ready source input clock) post Request.lengthTest 81#64 (Guest.GasLimit.le32 input 6 - 16 < 44) Request.requestBody test
    (DecoderCall.original_fail_code source.code environment.code) (environment.shapes .SszErr) result run notTimeout
  rcases outcome with stopped | passed
  · exact Or.inl stopped
  · exact Or.inr ⟨by omega,passed.2⟩

end InitECandidate.Solver.Input.Main.RequestPrefix

#print axioms InitECandidate.Solver.Input.Main.RequestPrefix.length_trace
