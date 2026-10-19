import InitECandidate.Solver.Rlp.SlicesNormal
import InitECandidate.Solver.Rlp.SlicesInputFrame

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem body_input (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (inputBase pointer length heap cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat)
    (sizeBound : 16*length.toNat<2^64)
    (copied : Input.Blob.HeapInput source input inputBase) (aligned : inputBase.toNat%8=0)
    (scratchBelow : cursor.toNat≤inputBase.toNat) (inputAbove : inputBase.toNat≤pointer.toNat)
    (copiedBefore : inputBase.toNat+input.length%2^64≤heap.toNat)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) : Input.Blob.HeapInput target input inputBase := by
  obtain ⟨items,count,itemModel,countEq,countBound,answer,records,room,nextArena,nextHeap,frame,price⟩ :=
    body_normal source target pointer length heap cursor limit inputBase.toNat pointerCell lengthCell arena heapGlobal heapBound before sizeBound
      aligned scratchBelow inputAbove installed value normal
  have fields := Input.evaluation_fields source target body (some (.returned value)) normal
  exact copied_input_frame source target input inputBase cursor.toNat heap.toNat (heap.toNat+16*count.toNat)
    copied aligned scratchBelow copiedBefore heap.isLt frame fields.1 fields.2.1

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.body_input
