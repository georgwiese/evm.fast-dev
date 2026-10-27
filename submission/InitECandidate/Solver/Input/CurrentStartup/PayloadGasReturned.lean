import InitECandidate.Solver.Input.CurrentStartup.WithdrawalReturn
import InitECandidate.Solver.Input.PayloadRemainingExecute
import InitECandidate.Solver.Input.PayloadPassingEntry

namespace InitECandidate.Solver.Input.CurrentStartup.PayloadGasReturned
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- The actual payload suffix returns its real record, with original copied
input and gas field. This is a reachable returned suffix, not a bound for main. -/
theorem withdrawal (input : Guest.InputBlob) (actual : WithdrawalReturn.Reached input) :
    ∃ source post, ∃ pointer record : BitVec 64, ∃ value : ValueHOL 64,
      evaluateHOLFiniteState source Payload.afterWithdrawals = (some (.returned value), post) ∧
      value = .val (.word record) ∧ Blob.HeapInput post input pointer ∧
      post.memory (record + 88#64) = .word (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)) ∧
      source.clock = post.clock ∧ NormalHeapEffects.AtLeast (record.toNat + 136) post ∧
      ∃ length, PayloadEntry.Endpoint input post pointer length value := by
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
  refine ⟨source, post, pointer, record, value, data.returned, valueEq, ?_, ?_, ?_, ?_, ⟨length, data.endpoint⟩⟩
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
  obtain ⟨source, post, pointer, record, value, run, valueEq, image, cell, clock, heap, length, endpoint⟩ :=
    withdrawal input (WithdrawalReturn.separated input word actual)
  obtain ⟨request, payload⟩ := CanonicalRequest.separated_offsets input word actual
  rw [valueEq] at run
  exact ⟨source, post, pointer, record, BitVec.ofNat 64 (Guest.GasLimit.le64 input 474), run, image, cell,
    Payload.stored_gas_bound input request payload gas, clock, heap⟩

/-- The suffix endpoint is the complete actual decoder poststate, up to
local-scope restoration. Thus its physical gas word and copied image survive
at the complete payload return, not just at an intermediate suffix. -/
theorem complete (input : Guest.InputBlob) (actual : WithdrawalReturn.Reached input) :
    ∃ entry post, ∃ pointer record : BitVec 64, ∃ length : Nat,
      PayloadEntry.Result input entry post pointer length (.val (.word record)) ∧
      evaluateHOLFiniteState entry Payload.body = (some (.returned (.val (.word record))), post) ∧
      Blob.HeapInput post input pointer ∧
      post.memory (record + 88#64) = .word (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)) ∧
      NormalHeapEffects.AtLeast (record.toNat + 136) post := by
  obtain ⟨source, suffixPost, pointer, record, value, suffixRun, valueEq, image, cell, clock, heap, length, endpoint⟩ := withdrawal input actual
  rw [valueEq] at endpoint
  obtain ⟨entry, post, entryFacts, frame, postClock⟩ := endpoint
  have original := entryFacts
  obtain ⟨lengthBound, code, shapes, domain, endian, entryImage, entryHeap, workspace, lower, aligned, room,
    p, n, extent, minimum, sliceUpper, sliceEq, returned, invocation⟩ := entryFacts
  have lengthSmall : length < 2^64 := by have := Nat.mod_lt input.length (show 0 < 2^64 by decide); omega
  have passed := Payload.passing_entry entry (BitVec.ofNat 64 length) n
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthSmall]; exact minimum)
  have memory : post.memory = suffixPost.memory := LocalEffects.memory_of_erase suffixPost post frame
  have domainFrame : post.memaddrs = suffixPost.memaddrs := by
    have field := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) frame
    exact field
  have endianFrame : post.be = suffixPost.be := by
    have field := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) frame
    exact field
  have globals : post.globals = suffixPost.globals := by
    have field := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) frame
    exact field
  refine ⟨entry, post, pointer, record, length, original, passed.trans returned,
    Blob.HeapInput.of_fields suffixPost post input pointer memory.symm domainFrame.symm endianFrame.symm image, ?_, ?_⟩
  · rw [memory]
    exact cell
  · obtain ⟨cursor, cursorCell, low, high, cursorAligned⟩ := heap
    exact ⟨cursor, (congrArg (fun table => table.lookup (Flapjack.Basis.Pure.MlString.ofString "heap_ptr")) globals).trans cursorCell,
      low, high, cursorAligned⟩

theorem separated_complete (input : Guest.InputBlob) (word : BitVec 64)
    (actual : MainSeparatedInput.StatelessRun input word)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
    ∃ entry post, ∃ pointer record gasWord : BitVec 64, ∃ length : Nat,
      PayloadEntry.Result input entry post pointer length (.val (.word record)) ∧
      evaluateHOLFiniteState entry Payload.body = (some (.returned (.val (.word record))), post) ∧
      Blob.HeapInput post input pointer ∧ post.memory (record + 88#64) = .word gasWord ∧ gasWord.toNat ≤ 200000000 ∧
      NormalHeapEffects.AtLeast (record.toNat + 136) post := by
  obtain ⟨entry, post, pointer, record, length, original, returned, bytes, cell, heap⟩ :=
    complete input (WithdrawalReturn.separated input word actual)
  obtain ⟨request, payload⟩ := CanonicalRequest.separated_offsets input word actual
  exact ⟨entry, post, pointer, record, BitVec.ofNat 64 (Guest.GasLimit.le64 input 474), length,
    original, returned, bytes, cell, Payload.stored_gas_bound input request payload gas, heap⟩

end InitECandidate.Solver.Input.CurrentStartup.PayloadGasReturned

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadGasReturned.withdrawal
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadGasReturned.separated

#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadGasReturned.complete
#print axioms InitECandidate.Solver.Input.CurrentStartup.PayloadGasReturned.separated_complete
