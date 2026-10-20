import InitECandidate.Solver.Input.PayloadAllocatedImage
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- All original physical payload words and transaction records refer to the
observed actual poststate at any clock budget; exact semantic padding removes
the prefix funding premise without changing data, memory, globals or FFI. -/
theorem allocated_image_any_clock (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor length : BitVec 64) (heap : Blob.HeapInput source input pointer) (extent : 602≤input.length%2^64)
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
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterGuard=(some (.returned value),post)) :
    Image post input pointer cursor length (PersistentAlloc.rounded cursor 136#64) ∧
      VarList.Records post input pointer (PersistentAlloc.rounded cursor 136#64) (62+Guest.GasLimit.le32 input 566) (transactionBytes input) ∧
      InitializerAllocations.context post=InitializerAllocations.context source ∧ Layout input length := by
  have paddedRun := panPropsEvaluateAddClockEq afterGuard source (some (.returned value)) post 8 ⟨run,by intro impossible; cases impossible⟩
  obtain ⟨image,records,context,layout⟩ := allocated_image {source with clock:=source.clock+8} {post with clock:=post.clock+8}
    input pointer cursor length heap extent p n inside domain pointerAligned cursorAligned pointerLower cursorAfter cursorRoom heapGlobal allocCode
    array arrayGlobal arrayAligned arrayLower arrayBefore offsetCode divisionCode failCode exceptionShape varCode fixedCode (by change 8≤source.clock+8; omega) value paddedRun
  exact ⟨Image.of_memory _ post input pointer cursor length (PersistentAlloc.rounded cursor 136#64) rfl image,
    VarList.Records.of_memory _ post input pointer (PersistentAlloc.rounded cursor 136#64) _ _ rfl records,context,layout⟩

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.allocated_image_any_clock
