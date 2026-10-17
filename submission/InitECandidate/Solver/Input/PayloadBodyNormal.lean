import InitECandidate.Solver.Input.PayloadAllocatedNormal

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole actual payload body. A normal return itself establishes the fixed
540-byte payload minimum and enough copied input for all scalar fields. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
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
    (enough : (input.length%2^64)/4+76≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word cursor) ∧ post.memory (cursor+88#64)=.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)) ∧
      Blob.HeapInput post input pointer ∧ source.clock-((input.length%2^64)/4+75)≤post.clock ∧ post.clock≤source.clock ∧ post.memory (cursor+56#64)=.word (BitVec.ofNat 64 (withdrawalCount input)) := by
  have entry:=entry_execute source length n failCode exceptionShape (by omega)
  by_cases short : length.toNat<540
  · rw [if_pos short] at entry
    rw [entry] at run
    have impossible:=congrArg Prod.fst run
    cases impossible
  · rw [if_neg short] at entry
    have extent : 602≤input.length%2^64 := by omega
    exact allocated_normal source post input pointer cursor length heap extent p n inside domain pointerAligned cursorAligned pointerLower cursorAfter cursorRoom
      heapGlobal allocCode array arrayGlobal arrayAligned arrayLower arrayBefore offsetCode divisionCode failCode exceptionShape varCode fixedCode enough value (entry.symm.trans run)

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.body_normal
