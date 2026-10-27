import InitECandidate.Solver.Input.BytesList.NormalAnyClock
import InitECandidate.Solver.Input.BytesList.RoomFromReturn
import InitECandidate.Solver.Input.AllocationHeapControl
import InitECandidate.Solver.Input.CurrentStartup.AllocationCursor
import InitECandidate.Solver.Input.DecoderRuntimeCode
import InitECandidate.Solver.Input.OriginalExceptions

namespace InitECandidate.Solver.Input.CurrentStartup.ByteListData
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

structure Result (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array limit maximum : BitVec 64) (start length floor : Nat) (value : ValueHOL 64) : Prop where
  heapCell : source.globals.lookup (ofString "heap_ptr") = some (.val (.word array))
  arrayLower : floor ≤ array.toNat
  arrayAligned : array.toNat % 8 = 0
  arrayBound : array.toNat ≤ 2952790016
  tuple : value = BytesList.pairValue (VarList.decodedArray array length) (VarList.decodedCount input start length)
  records : VarList.Records post input pointer array start length
  countLimit : VarList.decodedCount input start length ≤ limit.toNat
  lengths : ∀ index < VarList.decodedCount input start length,
    (VarList.recordLength input start length (VarList.decodedCount input start length) index).toNat ≤ maximum.toNat
  image : Blob.HeapInput post input pointer
  memory : ∀ query : BitVec 64, query.toNat < array.toNat → post.memory query = source.memory query
  control : WitnessRadix.BackingLayout.control post = WitnessRadix.BackingLayout.control
    (if length = 0 then source else WitnessRadix.PersistentAlloc.post source array
      (BitVec.ofNat 64 (16 * (Guest.GasLimit.le32 input start / 4))))
  heapExtent : NormalHeapEffects.AtLeast (array.toNat + 16 * VarList.decodedCount input start length) post
  heap : NormalHeapEffects.AtLeast floor post
  price : source.clock - post.clock ≤ 2 * (length / 4) + 2
  clock : post.clock ≤ source.clock

/-- Whole current byte-list return with real allocation room and a bounded
post-frontier. Empty and nonempty slices work at any actually returning clock. -/
theorem normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer limit maximum : BitVec 64) (start length floor : Nat)
    (installed : OriginalCode.Installed source.code) (shapes : OriginalExceptions.Installed source.eshapes)
    (domain : source.memaddrs = InitE.ordinaryDomain)
    (heap : NormalHeapEffects.AtLeast floor source) (afterInput : pointer.toNat + input.length % 2^64 + 8 ≤ floor)
    (image : Blob.HeapInput source input pointer) (inside : start + length ≤ input.length % 2^64)
    (lower : 2701131776 ≤ pointer.toNat) (aligned : pointer.toNat % 8 = 0)
    (inputBound : input.length % 2^64 ≤ Guest.maxInputBytes)
    (p : source.locals.lookup (ofString "p") = some (.val (.word (pointer + BitVec.ofNat 64 start))))
    (n : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))))
    (l : source.locals.lookup (ofString "lim") = some (.val (.word limit)))
    (m : source.locals.lookup (ofString "maxb") = some (.val (.word maximum)))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source BytesList.body = (some (.returned value), post)) :
    ∃ array, Result input source post pointer array limit maximum start length floor value := by
  obtain ⟨array, cell, low, high, arrayAligned⟩ := heap
  have room : array.toNat + 4 * length ≤ 33806089496 := by
    change input.length % 2^64 ≤ 1073741808 at inputBound
    omega
  obtain ⟨tuple, records, countLimit, bytes, lengths, lowerClock, upperClock, memory, control⟩ :=
    BytesList.normal_summary_any_clock source post input pointer array limit maximum start length image inside p n l domain
      lower aligned arrayAligned (by omega) room cell high (trap_entry source.code installed)
      (allocation_entry source.code installed) (DecoderRuntime.fail_code source.code installed) (shapes .SszErr)
      (DecoderRuntime.var_list_code source.code installed) m value actual
  have actualRoom (nonempty : length ≠ 0) : array.toNat + 16 * (Guest.GasLimit.le32 input start / 4) ≤ 2952790016 := by
    obtain ⟨observed, observedCell, observedLow, observedAligned, actualRoom⟩ :=
      (BytesList.room_from_return input source post pointer limit start length floor
        (allocation_entry source.code installed) (trap_entry source.code installed) (DecoderRuntime.fail_code source.code installed)
        (shapes .SszErr) (DecoderRuntime.var_list_code source.code installed) ⟨array, cell, low, high, arrayAligned⟩
        image inside p n l value actual).resolve_left nonempty
    have same : observed = array := by
      have equal := Option.some.inj (observedCell.symm.trans cell)
      cases equal
      rfl
    subst observed
    exact actualRoom
  let amount := BitVec.ofNat 64 (16 * VarList.decodedCount input start length)
  have amountNat : amount.toNat = 16 * VarList.decodedCount input start length := by
    by_cases empty : length = 0
    · simp [amount, VarList.decodedCount, empty]
    · have allocated := actualRoom empty
      dsimp only [amount]
      simp only [VarList.decodedCount, if_neg empty]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have extentControl : WitnessRadix.BackingLayout.control post = WitnessRadix.BackingLayout.control
      (if length = 0 then source else WitnessRadix.PersistentAlloc.post source array amount) := by
    by_cases empty : length = 0
    · simpa only [if_pos empty] using control
    · simpa only [if_neg empty, amount, VarList.decodedCount] using control
  have heapExtent : NormalHeapEffects.AtLeast (array.toNat + 16 * VarList.decodedCount input start length) post := by
    have returned := NormalHeapEffects.allocation_extent source post array amount (length = 0) cell high arrayAligned
      (by intro empty; simp [amount, VarList.decodedCount, empty]) (by
        intro nonempty
        rw [amountNat]
        simpa only [VarList.decodedCount, if_neg nonempty] using actualRoom nonempty) extentControl
    rw [amountNat] at returned
    exact returned
  have heapAfter : NormalHeapEffects.AtLeast floor post := by
    obtain ⟨cursor, cursorCell, cursorLow, cursorHigh, cursorAligned⟩ := heapExtent
    exact ⟨cursor, cursorCell, by omega, cursorHigh, cursorAligned⟩
  exact ⟨array, ⟨cell, low, arrayAligned, high, tuple, records, countLimit, lengths, bytes,
    memory, control, heapExtent, heapAfter, by omega, upperClock⟩⟩

end InitECandidate.Solver.Input.CurrentStartup.ByteListData

#print axioms InitECandidate.Solver.Input.CurrentStartup.ByteListData.normal
