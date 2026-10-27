import InitECandidate.Solver.Input.CurrentStartup.RequestsCountsEntry
import InitECandidate.Solver.Input.Requests.CountsBody
import InitECandidate.Solver.Input.Requests.PassingEntry

namespace InitECandidate.Solver.Input.CurrentStartup.RequestsReturned
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Result (input : Guest.InputBlob) (caller entry post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord requestRecord : BitVec 64) (payloadLength start size : Nat) (counts : Nat → BitVec 64) : Prop where
  origin : RequestsEntry.Result input caller entry post pointer statelessRecord record gasWord payloadLength start size (.val (.word requestRecord))
  returned : evaluateHOLFiniteState entry Requests.body = (some (.returned (.val (.word requestRecord))), post)
  image : Blob.HeapInput post input pointer
  heap : NormalHeapEffects.AtLeast (requestRecord.toNat + 80) post
  requestAfter : record.toNat + 136 ≤ requestRecord.toNat
  requestAligned : requestRecord.toNat % 8 = 0
  requestRoom : requestRecord.toNat + 80 ≤ 2952790016
  control : WitnessRadix.BackingLayout.control post = WitnessRadix.BackingLayout.control (WitnessRadix.PersistentAlloc.post entry requestRecord 80#64)
  gasCell : post.memory (record + 88#64) = .word gasWord
  price : entry.clock - post.clock ≤ 348
  clock : post.clock ≤ entry.clock
  cells : ∀ index < 5, post.memory (requestRecord + BitVec.ofNat 64 (16 * index)) =
      .word (pointer + BitVec.ofNat 64 start + Requests.offsetWord input start index) ∧
    post.memory (requestRecord + BitVec.ofNat 64 (16 * index + 8)) = .word (counts index)
  arithmetic : ∀ index < 5, (counts index).toNat =
      (Requests.countSpan (Requests.offsetWord input start) (BitVec.ofNat 64 size) index).toNat / (Requests.elementSize index).toNat ∧
    (Requests.countSpan (Requests.offsetWord input start) (BitVec.ofNat 64 size) index).toNat % (Requests.elementSize index).toNat = 0

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ caller entry post, ∃ pointer statelessRecord record gasWord requestRecord : BitVec 64,
    ∃ payloadLength start size : Nat, ∃ counts : Nat → BitVec 64,
      Result input caller entry post pointer statelessRecord record gasWord requestRecord payloadLength start size counts

/-- All five real counts/output stores join to the complete current request
return, retaining exact fields, copied input, heap ownership and protected gas.
The original normal request body spends at most348source call/loop ticks. -/
theorem counts (input : Guest.InputBlob) (actual : RequestsCountsEntry.Reached input) : Reached input := by
  obtain ⟨caller, source, suffixPost, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, start, size, value, data⟩ := actual
  have context := data.context
  have afterInput : pointer.toNat + input.length % 2^64 + 8 ≤ requestRecord.toNat := by
    have := context.statelessLower
    have := context.recordAfter
    have := data.requestAfter
    omega
  have arena : WitnessRadix.AllocatedBytes.Arena requestRecord 80 := ⟨by
    have := context.pointerLower
    have := data.requestAfter
    omega, by have := data.requestRoom; omega⟩
  rcases Requests.counts_body source suffixPost input pointer (pointer + BitVec.ofNat 64 start) requestRecord (BitVec.ofNat 64 size)
    (Requests.offsetWord input start) data.model data.code (data.shapes .SszErr) data.image data.domain arena
    context.pointerAligned data.requestAligned afterInput (some (.returned value)) data.returned (by simp) with rejected | completed
  · obtain ⟨error, allowed, impossible, price⟩ := rejected
    cases impossible
  · obtain ⟨same, image, price, clock, control, outside, counts, cells, arithmetic⟩ := completed
    have valueEq : value = .val (.word requestRecord) := by cases same; rfl
    have globals : suffixPost.globals = source.globals := by
      have field := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) control
      exact field
    have suffixHeap : NormalHeapEffects.AtLeast (requestRecord.toNat + 80) suffixPost := by
      obtain ⟨cursor, cell, low, high, aligned⟩ := data.heap
      exact ⟨cursor, (congrArg (fun table => table.lookup (ofString "heap_ptr")) globals).trans cell, low, high, aligned⟩
    have gasNat : (record + 88#64).toNat = record.toNat + 88 := by
      rw [BitVec.toNat_add_of_lt (by change record.toNat + 88 < 2^64; have := context.recordRoom; omega)]
      rfl
    have gasFrame := outside (record + 88#64) (Or.inl (by rw [gasNat]; have := data.requestAfter; omega))
    have suffixGas := gasFrame.trans data.gasCell
    obtain ⟨entry, post, original, allocationControl, prefixForward, prefixPrice, frame, postClock⟩ := data.endpoint
    rw [valueEq] at original
    have lengthSmall : size < 2^64 := by
      have := data.inside
      have := Nat.mod_lt input.length (show 0 < 2^64 by decide)
      omega
    have full := (Requests.passing_entry entry (BitVec.ofNat 64 size) original.len
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt lengthSmall]; exact original.minimum)).trans original.returned
    have memory : post.memory = suffixPost.memory := LocalEffects.memory_of_erase suffixPost post frame
    have domain : post.memaddrs = suffixPost.memaddrs := by
      have field := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) frame
      exact field
    have endian : post.be = suffixPost.be := by
      have field := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) frame
      exact field
    have rootGlobals : post.globals = suffixPost.globals := by
      have field := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) frame
      exact field
    have rootControl : WitnessRadix.BackingLayout.control post = WitnessRadix.BackingLayout.control suffixPost := by
      have same := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => WitnessRadix.BackingLayout.control state) frame
      exact same
    refine ⟨caller, entry, post, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, start, size, counts,
      ⟨original, full, Blob.HeapInput.of_fields suffixPost post input pointer memory.symm domain.symm endian.symm image,
        ?_, data.requestAfter, data.requestAligned, data.requestRoom, rootControl.trans (control.trans allocationControl), ?_, ?_, ?_, ?_, arithmetic⟩⟩
    · obtain ⟨cursor, cell, low, high, aligned⟩ := suffixHeap
      exact ⟨cursor, (congrArg (fun table => table.lookup (ofString "heap_ptr")) rootGlobals).trans cell, low, high, aligned⟩
    · rw [memory]
      exact suffixGas
    · rw [postClock]
      omega
    · rw [postClock]
      omega
    · intro index small
      rw [memory]
      exact cells index small

theorem separated (input : Guest.InputBlob) (word : BitVec 64)
    (actual : MainSeparatedInput.StatelessRun input word)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached input :=
  counts input (RequestsCountsEntry.separated input word actual gas)

end InitECandidate.Solver.Input.CurrentStartup.RequestsReturned

#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestsReturned.counts
#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestsReturned.separated
