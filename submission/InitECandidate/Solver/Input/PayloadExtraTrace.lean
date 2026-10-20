import InitECandidate.Solver.Input.PayloadExtraGuard
import InitECandidate.Solver.Input.SszGuardTrace

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual extra-data guard for any non-timeout payload execution. Invalid
extra length raises its real SszErr51 with a funded one-tick call; passing
reaches the original afterExtra body without changing the current state. -/
theorem extra_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (e : source.locals.lookup (ofString "o_extra") = some (.val (.word 540#64)))
    (t : source.locals.lookup (ofString "o_txs") = some (.val (.word (offsetWords input 1))))
    (lower : 540 ≤ (offsetWords input 1).toNat)
    (failCode : source.code.lookup (ofString "ssz_fail") = some (SszFail.formals,SszFail.body,.one))
    (shape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source offsetContinuation = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (32 < (offsetWords input 1).toNat - 540 ∧ 1 ≤ source.clock ∧ result = some (.exception (ofString "SszErr") (.val (.word 51#64))) ∧
      post = emptyLocalsHOLFinite {source with clock := source.clock - 1}) ∨
    ((offsetWords input 1).toNat - 540 ≤ 32 ∧ evaluateHOLFiniteState source afterExtra = (result,post)) := by
  have test := extra_test_read source input e t lower
  rw [extra_shape] at run
  rcases Header.guard_trace source post extraTest 51#64 (32 < (offsetWords input 1).toNat - 540) afterExtra test failCode shape result run notTimeout with short | valid
  · exact Or.inl short
  · exact Or.inr ⟨by omega,valid.2⟩

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.extra_trace
