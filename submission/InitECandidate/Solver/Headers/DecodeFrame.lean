import InitECandidate.Solver.Headers.DecodeSlices
import InitECandidate.Solver.Input.HashInputRegion
import InitECandidate.Solver.Rlp.SlicesInputFrame

namespace InitECandidate.Solver.Headers.Decode
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Compose both actual RLP footprints. Scratch writes stay below the
incoming cursor and new records are confined to the real slice allocation. -/
theorem prefix_memory (source parsed sliced : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length header payload heap cursor limit count : BitVec 64) (items : List Rlp.ListItem)
    (topReturned : Rlp.Decode.Returned source parsed pointer length cursor limit (Rlp.Item.result pointer header payload 1#64))
    (slicesReturned : Rlp.Slices.Returned (topState source parsed pointer header payload) sliced (pointer+header) payload heap cursor limit count items) :
    ∀ query : BitVec 64,cursor.toNat≤query.toNat → query.toNat<heap.toNat ∨ heap.toNat+16*count.toNat≤query.toNat →
      sliced.memory query=source.memory query := by
  intro query beyond outside
  exact (slicesReturned.memory query beyond outside).trans (topReturned.memory query beyond)

/-- In particular, every copied/decoded word before the entry heap survives
this original header prefix, including unrelated witness and SI records. -/
theorem prefix_input_frame (source parsed sliced : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length header payload heap cursor limit count : BitVec 64) (items : List Rlp.ListItem) (lower upper : Nat)
    (topReturned : Rlp.Decode.Returned source parsed pointer length cursor limit (Rlp.Item.result pointer header payload 1#64))
    (slicesReturned : Rlp.Slices.Returned (topState source parsed pointer header payload) sliced (pointer+header) payload heap cursor limit count items)
    (afterScratch : cursor.toNat≤lower) (beforeHeap : upper≤heap.toNat) : Input.HashInput.Frame source sliced lower upper := by
  refine ⟨?_⟩
  intro query low high
  exact prefix_memory source parsed sliced pointer length header payload heap cursor limit count items topReturned slicesReturned query
    (by omega) (Or.inl (by omega))

theorem prefix_globals (source parsed sliced : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length header payload heap cursor limit count : BitVec 64) (items : List Rlp.ListItem)
    (topReturned : Rlp.Decode.Returned source parsed pointer length cursor limit (Rlp.Item.result pointer header payload 1#64))
    (slicesReturned : Rlp.Slices.Returned (topState source parsed pointer header payload) sliced (pointer+header) payload heap cursor limit count items) :
    ∀ key,key≠ofString "heap_ptr" → sliced.globals.lookup key=source.globals.lookup key := by
  intro key other
  exact (slicesReturned.globals key other).trans (topReturned.globals key)

/-- The entire actual copied input survives; the input extent is modulo
2^64 as in the original guest, independently of mathematical list length. -/
theorem prefix_copied_input (source parsed sliced : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (inputBase pointer length header payload heap cursor limit count : BitVec 64) (items : List Rlp.ListItem)
    (topReturned : Rlp.Decode.Returned source parsed pointer length cursor limit (Rlp.Item.result pointer header payload 1#64))
    (slicesReturned : Rlp.Slices.Returned (topState source parsed pointer header payload) sliced (pointer+header) payload heap cursor limit count items)
    (copied : Input.Blob.HeapInput source input inputBase) (aligned : inputBase.toNat%8=0)
    (afterScratch : cursor.toNat≤inputBase.toNat) (beforeHeap : inputBase.toNat+input.length%2^64≤heap.toNat) :
    Input.Blob.HeapInput sliced input inputBase := by
  have domain : sliced.memaddrs=source.memaddrs := slicesReturned.domain.trans topReturned.domain
  have endian : sliced.be=source.be := slicesReturned.endian.trans topReturned.endian
  exact Rlp.Slices.copied_input_frame source sliced input inputBase inputBase.toNat heap.toNat (heap.toNat+16*count.toNat) copied aligned
    (Nat.le_refl _) beforeHeap heap.isLt
    (fun query beyond outside=>prefix_memory source parsed sliced pointer length header payload heap cursor limit count items
      topReturned slicesReturned query (afterScratch.trans beyond) outside) domain endian

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.prefix_memory
#print axioms InitECandidate.Solver.Headers.Decode.prefix_input_frame
#print axioms InitECandidate.Solver.Headers.Decode.prefix_globals
#print axioms InitECandidate.Solver.Headers.Decode.prefix_copied_input
