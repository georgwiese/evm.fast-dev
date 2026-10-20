import InitECandidate.Solver.Input.PayloadBodyNormal
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Apply the complete original normal-payload proof to its actual execution
at any clock budget. Exact semantic clock padding removes the sufficient-
clock premise; return value, real gas/count cells and every byte remain the
actual unpadded poststate. The source allowance is encodedLength/4+75. -/
theorem body_normal_any_clock (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor length : BitVec 64) (heap : Blob.HeapInput source input pointer)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (inside : 62+length.toNat≤input.length%2^64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (cursorAligned : cursor.toNat%8=0)
    (pointerLower : 2701131776≤pointer.toNat)
    (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+136+4*(input.length%2^64)≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (array : BitVec 64) (arrayGlobal : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (arrayAligned : array.toNat%8=0) (arrayLower : 2701131776≤array.toNat) (arrayBefore : array.toNat+64≤pointer.toNat)
    (offsetCode : source.code.lookup (ofString "ssz_check_offsets")=some (Offsets.formals,Offsets.body,.one))
    (divisionCode : source.code.lookup (ofString "udivmod")=some (UDivMod.formals,UDivMod.body,UDivMod.returnShape))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (varCode : source.code.lookup (ofString "ssz_split_var_list")=some (VarList.formals,VarList.body,VarList.returnShape))
    (fixedCode : source.code.lookup (ofString "ssz_fixed_list_count")=some (FixedList.formals,FixedList.body,.one))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body = (some (.returned value),post)) :
    value = .val (.word cursor) ∧ post.memory (cursor + 88#64) = .word (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)) ∧
      Blob.HeapInput post input pointer ∧ source.clock - post.clock ≤ (input.length % 2^64) / 4 + 75 ∧ post.clock ≤ source.clock ∧
      post.memory (cursor + 56#64) = .word (BitVec.ofNat 64 (withdrawalCount input)) ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (nextHeap input (PersistentAlloc.rounded cursor 136#64)))) ∧ transactionCount input ≤ (input.length % 2^64) / 4 := by
  let padding := (input.length % 2^64) / 4 + 76
  have paddedRun := panPropsEvaluateAddClockEq body source (some (.returned value)) post padding ⟨run,by intro impossible; cases impossible⟩
  obtain ⟨returned,gasCell,paddedHeap,lower,upper,countCell,heapCursor,countBound⟩ := body_normal {source with clock := source.clock + padding} {post with clock := post.clock + padding}
    input pointer cursor length heap p n inside domain pointerAligned cursorAligned pointerLower cursorAfter cursorRoom heapGlobal allocCode array arrayGlobal arrayAligned arrayLower arrayBefore
    offsetCode divisionCode failCode exceptionShape varCode fixedCode (by change (input.length % 2^64) / 4 + 76 ≤ source.clock + padding; dsimp only [padding]; omega) value paddedRun
  have actualHeap := Blob.HeapInput.of_fields {post with clock := post.clock + padding} post input pointer rfl rfl rfl paddedHeap
  change source.clock + padding - ((input.length % 2^64) / 4 + 75) ≤ post.clock + padding at lower
  change post.clock + padding ≤ source.clock + padding at upper
  dsimp only [padding] at lower upper
  exact ⟨returned,gasCell,actualHeap,by omega,by omega,countCell,heapCursor,countBound⟩

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.body_normal_any_clock
