import InitECandidate.Solver.Input.PayloadTailNormal
import InitECandidate.Solver.Input.PayloadTransactionsNormal
import InitECandidate.Solver.Input.AllocationControl
import InitECandidate.Solver.Input.PayloadWithdrawalNumbers

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- All real payload work after the extra-data guard, including both list
calls and the actual gas-field store, on every normal return. -/
theorem after_extra_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor array length : BitVec 64) (heap : Blob.HeapInput source input pointer) (extent : 602≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word cursor)))
    (n : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (e : source.locals.lookup (ofString "o_extra")=some (.val (.word 540#64)))
    (t : source.locals.lookup (ofString "o_txs")=some (.val (.word (offsetWords input 1))))
    (w : source.locals.lookup (ofString "o_wd")=some (.val (.word (offsetWords input 2))))
    (b : source.locals.lookup (ofString "o_bal")=some (.val (.word (offsetWords input 3))))
    (valid : ∀ position<4,Offsets.ValidAt 540#64 length (offsetWords input) position)
    (inside : 62+length.toNat≤input.length%2^64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (cursorAligned : cursor.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (pointerLower : 2701131776≤pointer.toNat)
    (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+136≤33806089496)
    (arrayAfter : pointer.toNat+input.length%2^64+8≤array.toNat)
    (room : array.toNat+4*(Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word array)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (divisionCode : source.code.lookup (ofString "udivmod")=some (UDivMod.formals,UDivMod.body,UDivMod.returnShape))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (varCode : source.code.lookup (ofString "ssz_split_var_list")=some (VarList.formals,VarList.body,VarList.returnShape))
    (fixedCode : source.code.lookup (ofString "ssz_fixed_list_count")=some (FixedList.formals,FixedList.body,.one))
    (enough : (Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)/4+69≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterExtra=(some (.returned value),post)) :
    value=.val (.word cursor) ∧ post.memory (cursor+88#64)=.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)) ∧
      Blob.HeapInput post input pointer ∧
      source.clock-((Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566)/4+68)≤post.clock ∧ post.clock≤source.clock ∧ post.memory (cursor+56#64)=.word (BitVec.ofNat 64 (withdrawalCount input)) := by
  classical
  obtain ⟨next,innerPost,returned,valueEq,localsEq,nextHeap,oldMemory,clockLower,clockUpper,controlEq,nextRun,postEq⟩:=
    transactions_normal source post input pointer cursor array length heap p pl e t w valid inside domain pointerAligned cursorAligned arrayAligned
      pointerLower cursorAfter cursorRoom arrayAfter room heapGlobal allocCode failCode exceptionShape varCode (by omega) value run
  let empty:=Guest.GasLimit.le32 input 570=Guest.GasLimit.le32 input 566
  let records:=if empty then 0#64 else array
  let count:=if empty then 0#64 else BitVec.ofNat 64 (Guest.GasLimit.le32 input (62+Guest.GasLimit.le32 input 566)/4)
  have tupleEq : returned=UDivMod.pairValue records count := by
    rw [valueEq]
    by_cases isEmpty : empty
    · simp [empty,isEmpty,records,count,VarList.emptyValue,VarList.pairValue,UDivMod.pairValue]
    · simp [empty,isEmpty,records,count,VarList.emptyValue,VarList.pairValue,UDivMod.pairValue]
  have txs : next.locals.lookup (ofString "txs")=some (UDivMod.pairValue records count) := by
    rw [localsEq,tupleEq]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have localOther : ∀ name : String,ofString "txs"≠ofString name→next.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    intro name different
    rw [localsEq]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,different]
  obtain ⟨domainEq,codeEq,shapeEq⟩:=allocation_control_fields source next array
    (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input (62+Guest.GasLimit.le32 input 566)/4))) empty controlEq
  obtain ⟨finalValue,gasCell,finalHeap,finalLower,finalUpper,countCell⟩:=after_transactions_normal next innerPost input pointer cursor length records count
    (offsetWords input 2) (offsetWords input 3) nextHeap extent ((localOther "p" (by decide)).trans p) ((localOther "pl" (by decide)).trans pl)
    ((localOther "len" (by decide)).trans n) txs ((localOther "o_wd" (by decide)).trans w) ((localOther "o_bal" (by decide)).trans b)
    (domainEq.trans domain) pointerAligned cursorAligned pointerLower cursorAfter cursorRoom
    (by rw [codeEq]; exact divisionCode) (by rw [codeEq]; exact failCode) (by rw [shapeEq]; exact exceptionShape)
    (by rw [codeEq]; exact fixedCode) (by omega) value nextRun
  refine ⟨finalValue,?_,?_,?_,?_,?_⟩
  · rw [postEq]; exact gasCell
  · rw [postEq]; exact Blob.HeapInput.restore source innerPost input pointer "txs" finalHeap
  · have postClock : post.clock=innerPost.clock := by rw [postEq]; rfl
    omega
  · have postClock : post.clock=innerPost.clock := by rw [postEq]; rfl
    omega
  · rw [postEq]
    rw [(withdrawal_difference input length valid).2.1] at countCell
    exact countCell

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.after_extra_normal
