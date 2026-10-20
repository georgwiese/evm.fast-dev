import InitECandidate.Solver.Input.SerializeExecution
import InitECandidate.Solver.Input.ClockExhaustion

namespace InitECandidate.Solver.Input.Serialize
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem post_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out root succ chain schema : BitVec 64)
    (outAligned : out.toNat % 8 = 0) (rootAligned : root.toNat % 8 = 0) :
    (post source out root succ chain schema).clock = source.clock - 5 := by
  have mask : CopyGeneral.aligned root out := Copy32.alignment_mask root out rootAligned outAligned
  have price : CopyGeneral.cost root out 32 = 1 := by
    simp [CopyGeneral.cost,mask,CopyWords.prefixCost,CopyWords.prefixIndex,CopyBytes.suffixCost]
  simp only [post,schemaState,chained,succeeded,copied,CopyGeneral.callState,price,Nat.sub_sub]

theorem bound_and_return (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out root succ chain schema : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (outBinding : source.locals.lookup (ofString "out") = some (.val (.word out)))
    (rootBinding : source.locals.lookup (ofString "root") = some (.val (.word root)))
    (succBinding : source.locals.lookup (ofString "succ") = some (.val (.word succ)))
    (chainBinding : source.locals.lookup (ofString "chain_id") = some (.val (.word chain)))
    (schemaBinding : source.locals.lookup (ofString "schema_id") = some (.val (.word schema)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (outArena : AllocatedBytes.Arena out 43) (rootArena : AllocatedBytes.Arena root 32)
    (outAligned : out.toNat % 8 = 0) (rootAligned : root.toNat % 8 = 0) :
    source.clock - (evaluateHOLFiniteState source body).2.clock ≤ 5 ∧
      (∀ value target,evaluateHOLFiniteState source body = (some (.returned value),target) →
        value = .val (.word 43#64) ∧ target = emptyLocalsHOLFinite (post source out root succ chain schema)) := by
  by_cases enough : 5 ≤ source.clock
  · have run := execute source out root succ chain schema installed outBinding rootBinding succBinding chainBinding schemaBinding domain outArena rootArena outAligned rootAligned enough
    refine ⟨?_,?_⟩
    · rw [run]
      change source.clock - (post source out root succ chain schema).clock ≤ 5
      rw [post_clock source out root succ chain schema outAligned rootAligned]
      omega
    · intro value target actual
      have same := run.symm.trans actual
      have result := congrArg Prod.fst same
      have endpoint := congrArg Prod.snd same
      exact ⟨by simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using result.symm,endpoint.symm⟩
  · have padded := execute {source with clock := source.clock + 5} out root succ chain schema installed outBinding rootBinding succBinding chainBinding schemaBinding domain outArena rootArena outAligned rootAligned (by simp)
    have remainder : (emptyLocalsHOLFinite (post {source with clock := source.clock + 5} out root succ chain schema)).clock < 5 := by
      rw [show (emptyLocalsHOLFinite (post {source with clock := source.clock + 5} out root succ chain schema)).clock = (post {source with clock := source.clock + 5} out root succ chain schema).clock from rfl,
        post_clock _ out root succ chain schema outAligned rootAligned]
      change source.clock + 5 - 5 < 5
      omega
    have timeout := timeout_of_padded_remainder source _ body 5 _ padded remainder
    refine ⟨by omega,?_⟩
    intro value target actual
    rw [actual] at timeout
    cases timeout

end InitECandidate.Solver.Input.Serialize

#print axioms InitECandidate.Solver.Input.Serialize.post_clock
#print axioms InitECandidate.Solver.Input.Serialize.bound_and_return
