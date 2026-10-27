import InitECandidate.Solver.Input.CurrentStartup.WithdrawalReturn
import InitECandidate.Solver.Input.PayloadRemainingExecute

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadGasReturned
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- The actual payload suffix returns its real record, with original copied
input and gas field. This is a reachable returned suffix, not a bound for main. -/
theorem withdrawal (input : Guest.InputBlob) (actual : WithdrawalReturn.Reached input) :
    ∃ source post, ∃ pointer record : BitVec 64, ∃ value : ValueHOL 64,
      evaluateHOLFiniteState source Payload.afterWithdrawals = (some (.returned value), post) ∧
      value = .val (.word record) ∧ Blob.HeapInput post input pointer ∧
      post.memory (record + 88#64) = .word (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)) ∧
      source.clock = post.clock ∧ NormalHeapEffects.AtLeast (record.toNat + 136) post := by
  obtain ⟨origin, source, post, pointer, record, array, count, length, start, size, value, data⟩ := actual
  have context := data.context
  have completed := Payload.remaining_execute source input pointer record (BitVec.ofNat 64 length)
    (Payload.offsetWords input 2) (Payload.offsetWords input 3) count context.image context.extent context.p context.pl
    context.len context.wd context.bal data.nwd context.domain context.aligned context.recordAligned
    (by have := context.lower; omega) context.recordLower (by have := context.recordRoom; omega)
  have same := completed.1.symm.trans data.returned
  have valueEq : value = .val (.word record) := by
    have eq := congrArg Prod.fst same
    cases eq
    rfl
  have postEq := (congrArg Prod.snd same).symm
  dsimp only at postEq
  refine ⟨source, post, pointer, record, value, data.returned, valueEq, ?_, ?_, ?_, ?_⟩
  · rw [postEq]
    exact completed.2.1
  · rw [postEq]
    exact completed.2.2.2.1
  · rw [postEq]
    exact completed.2.2.1.symm
  · rw [postEq]
    exact context.recordHeap

/-- Whole-main-derived reachability and the original declared-gas premise
now meet at the actual returned suffix's physical gas cell. -/
theorem separated (input : Guest.InputBlob) (word : BitVec 64)
    (actual : MainSeparatedInput.StatelessRun input word)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
    ∃ source post, ∃ pointer record gasWord : BitVec 64,
      evaluateHOLFiniteState source Payload.afterWithdrawals = (some (.returned (.val (.word record))), post) ∧
      Blob.HeapInput post input pointer ∧ post.memory (record + 88#64) = .word gasWord ∧ gasWord.toNat ≤ 200000000 ∧
      source.clock = post.clock ∧ NormalHeapEffects.AtLeast (record.toNat + 136) post := by
  obtain ⟨source, post, pointer, record, value, run, valueEq, image, cell, clock, heap⟩ :=
    withdrawal input (WithdrawalReturn.separated input word actual)
  obtain ⟨request, payload⟩ := CanonicalRequest.separated_offsets input word actual
  rw [valueEq] at run
  exact ⟨source, post, pointer, record, BitVec.ofNat 64 (Guest.GasLimit.le64 input 474), run, image, cell,
    Payload.stored_gas_bound input request payload gas, clock, heap⟩

end InitECandidate.Solver.Input.CurrentStartup.PayloadGasReturned

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadGasReturned.withdrawal
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadGasReturned.separated
