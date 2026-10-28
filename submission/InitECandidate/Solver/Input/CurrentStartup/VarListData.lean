import InitECandidate.Solver.Input.CurrentStartup.VarListRoom
import InitECandidate.Solver.Input.VarList.NormalAnyClock
import InitECandidate.Solver.Input.AllocationHeapControl

namespace InitECandidate.Solver.Input.CurrentStartup.VarListData
variable {decoderOrigin : DecoderOrigin}
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real returned transaction-list data, retaining its caller invocation
so that later proofs can resume the actual payload continuation. -/
structure Result (input : Guest.InputBlob) (caller entry post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record array : BitVec 64) (length start size : Nat) (value : ValueHOL 64) : Prop where
  context : PayloadWorkspace.Context input caller pointer record length
  hashPrefix : Payload.PrefixImage input caller pointer record
  valid : ∀ position < 4, Offsets.ValidAt 540#64 (BitVec.ofNat 64 length) (Payload.offsetWords input) position
  heapCell : entry.globals.lookup (ofString "heap_ptr") = some (.val (.word array))
  recordBefore : record.toNat + 136 ≤ array.toNat
  arrayAligned : array.toNat % 8 = 0
  arrayBound : array.toNat ≤ 2952790016
  startEq : start = 62 + Guest.GasLimit.le32 input 566
  sizeEq : size = Guest.GasLimit.le32 input 570 - Guest.GasLimit.le32 input 566
  inside : start + size ≤ input.length % 2^64
  returned : evaluateHOLFiniteState entry VarList.body = (some (.returned value), post)
  tuple : value = VarList.pairValue (VarList.decodedArray array size) (VarList.decodedCount input start size)
  bytes : Blob.HeapInput post input pointer
  records : VarList.Records post input pointer array start size
  memory : ∀ query : BitVec 64, query.toNat < array.toNat → post.memory query = entry.memory query
  control : WitnessRadix.BackingLayout.control post = WitnessRadix.BackingLayout.control
    (if size = 0 then entry else WitnessRadix.PersistentAlloc.post entry array
      (BitVec.ofNat 64 (16 * (Guest.GasLimit.le32 input start / 4))))
  heapExtent : NormalHeapEffects.AtLeast (array.toNat + 16 * VarList.decodedCount input start size) post
  heap : NormalHeapEffects.AtLeast (record.toNat + 136) post
  price : entry.clock - post.clock ≤ size / 4 + 1
  clock : post.clock ≤ entry.clock
  invocation : ∃ callee parentPost parentValue,
    entry = callEntryStateHOLFinite caller callee ∧
    evalListHOLFinite caller (h := fun address => Classical.propDecidable (caller.memaddrs address)) Payload.transactionArguments =
      some (VarList.values (pointer + BitVec.ofNat 64 start) (BitVec.ofNat 64 size) 9223372036854775807#64) ∧
    lookupCodeHOLFinite caller.code.lookup (ofString "ssz_split_var_list")
      (VarList.values (pointer + BitVec.ofNat 64 start) (BitVec.ofNat 64 size) 9223372036854775807#64) =
      some (VarList.body, callee, VarList.returnShape) ∧
    evaluateHOLFiniteState caller Payload.transactionCall = (some (.returned parentValue), parentPost) ∧
    PayloadEntry.Endpoint (decoderOrigin := decoderOrigin) input parentPost pointer record length parentValue

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ caller entry post, ∃ pointer record array : BitVec 64, ∃ length start size : Nat, ∃ value : ValueHOL 64,
    Result (decoderOrigin := decoderOrigin) input caller entry post pointer record array length start size value

theorem transaction (input : Guest.InputBlob) (actual : TransactionEntry.Reached (decoderOrigin := decoderOrigin) input) : Reached (decoderOrigin := decoderOrigin) input := by
  obtain ⟨caller, entry, post, pointer, record, length, start, size, value, context, hashPrefix, valid, installed, shapes, domain, endian,
    globals, image, heap, p, n, l, startEq, sizeEq, inside, returned, invocation⟩ := actual
  obtain ⟨array, cell, low, high, aligned⟩ := heap
  have afterInput : pointer.toNat + input.length % 2^64 + 8 ≤ array.toNat := by have := context.recordLower; omega
  have room : array.toNat + 4 * size ≤ 33806089496 := by
    have limit := context.lengthBound
    change input.length % 2^64 ≤ 1073741808 at limit
    omega
  obtain ⟨tuple, control, bytes, memory, records, countLimit, price, clock⟩ :=
    VarList.normal_summary_any_clock entry post input pointer array 9223372036854775807#64 start size image inside p n l domain
      (by have := context.lower; omega) context.aligned aligned afterInput room cell high (trap_entry entry.code installed)
      (allocation_entry entry.code installed) (CanonicalHeader.fail_code entry.code installed) (shapes .SszErr) value returned
  have actualRoom (nonempty : size ≠ 0) : array.toNat + 16 * (Guest.GasLimit.le32 input start / 4) ≤ 2952790016 := by
    obtain ⟨observed, observedCell, observedLow, observedAligned, minimum, positive, header, upper, limit, allocatedRoom⟩ :=
      (VarListRoom.returned_room input entry post pointer 9223372036854775807#64 start size (record.toNat + 136)
        installed shapes ⟨array, cell, low, high, aligned⟩ image inside p n l value returned).resolve_left
        (by intro no; exact nonempty no.1)
    have same : observed = array := by
      have eq := Option.some.inj (observedCell.symm.trans cell)
      cases eq
      rfl
    subst observed
    exact allocatedRoom
  let amount := BitVec.ofNat 64 (16 * VarList.decodedCount input start size)
  have amountNat : amount.toNat = 16 * VarList.decodedCount input start size := by
    by_cases empty : size = 0
    · simp [amount, VarList.decodedCount, empty]
    · have allocated := actualRoom empty
      dsimp only [amount]
      simp only [VarList.decodedCount, if_neg empty]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have extentControl : WitnessRadix.BackingLayout.control post = WitnessRadix.BackingLayout.control
      (if size = 0 then entry else WitnessRadix.PersistentAlloc.post entry array amount) := by
    by_cases empty : size = 0
    · simpa only [if_pos empty] using control
    · simpa only [if_neg empty, amount, VarList.decodedCount] using control
  have heapExtent : NormalHeapEffects.AtLeast (array.toNat + 16 * VarList.decodedCount input start size) post := by
    have returned := NormalHeapEffects.allocation_extent entry post array amount (size = 0) cell high aligned
      (by intro empty; simp [amount, VarList.decodedCount, empty]) (by
        intro nonempty
        rw [amountNat]
        simpa only [VarList.decodedCount, if_neg nonempty] using actualRoom nonempty) extentControl
    rw [amountNat] at returned
    exact returned
  have postHeap : NormalHeapEffects.AtLeast (record.toNat + 136) post := by
    obtain ⟨cursor, cursorCell, cursorLow, cursorHigh, cursorAligned⟩ := heapExtent
    exact ⟨cursor, cursorCell, by omega, cursorHigh, cursorAligned⟩
  exact ⟨caller, entry, post, pointer, record, array, length, start, size, value,
    ⟨context, hashPrefix, valid, cell, low, aligned, high, startEq, sizeEq, inside, returned, tuple, bytes, records, memory, control, heapExtent, postHeap, price, clock, invocation⟩⟩

theorem separated (input : Guest.InputBlob) (actual : MainSeparatedInput.RootRun input decoderOrigin) : Reached (decoderOrigin := decoderOrigin) input :=
  transaction input (TransactionEntry.separated input actual)

end InitECandidate.Solver.Input.CurrentStartup.VarListData

#print axioms InitECandidate.Solver.Input.CurrentStartup.VarListData.transaction
#print axioms InitECandidate.Solver.Input.CurrentStartup.VarListData.separated
