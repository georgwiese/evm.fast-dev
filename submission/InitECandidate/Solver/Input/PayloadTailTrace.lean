import InitECandidate.Solver.Input.PayloadTailNormal
import InitECandidate.Solver.Input.FixedList.CallerTrace

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Both actual transaction stores, real withdrawal-count call and every
remaining payload field/return, including SszErr30/31 at any actual clock. -/
theorem after_transactions_trace_image (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor length records transactionCount withdrawals balances : BitVec 64)
    (heap : Blob.HeapInput source input pointer) (inside : 602≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word cursor)))
    (n : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (txs : source.locals.lookup (ofString "txs")=some (UDivMod.pairValue records transactionCount))
    (w : source.locals.lookup (ofString "o_wd")=some (.val (.word withdrawals)))
    (b : source.locals.lookup (ofString "o_bal")=some (.val (.word balances)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (cursorAligned : cursor.toNat%8=0)
    (pointerLower : 2701131776≤pointer.toNat)
    (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+136≤33806089496)
    (divisionCode : source.code.lookup (ofString "udivmod")=some (UDivMod.formals,UDivMod.body,UDivMod.returnShape))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (code : source.code.lookup (ofString "ssz_fixed_list_count")=some (FixedList.formals,FixedList.body,.one))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterTransactions=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤67 ∧
      ((∃ error : BitVec 64,(error=30#64 ∨ error=31#64) ∧ result=some (.exception (ofString "SszErr") (.val (.word error)))) ∨ (result=some (.returned (.val (.word cursor))) ∧ ∃ count : BitVec 64,
        count.toNat=(balances-withdrawals).toNat/44 ∧ (balances-withdrawals).toNat%44=0 ∧
        post.memory=fieldMemory (transactionFieldsStored source cursor records transactionCount).memory cursor (remainingFields input pointer length withdrawals balances count) ∧
        WitnessRadix.BackingLayout.control post=WitnessRadix.BackingLayout.control source)) := by
  obtain ⟨prefixRun,prefixHeap⟩ := transaction_stores source input pointer cursor records transactionCount heap pl txs domain pointerAligned cursorAligned pointerLower cursorAfter cursorRoom
  let stored := transactionFieldsStored source cursor records transactionCount
  have args := withdrawal_arguments stored withdrawals balances w b
  have tailRun : evaluateHOLFiniteState stored withdrawalCall=(result,post) := prefixRun.symm.trans run
  rw [transactions_shape.2.2.2] at tailRun
  rcases FixedList.caller_trace stored post (balances-withdrawals) 44#64 9223372036854775807#64 (by decide) divisionCode failCode exceptionShape code
    "nwd" withdrawalArguments afterWithdrawals args result tailRun notTimeout with rejected | normal
  · obtain ⟨error,allowed,same,cost⟩ := rejected
    exact ⟨cost,Or.inl ⟨error,allowed,same⟩⟩
  obtain ⟨next,innerPost,count,localsEq,countBound,forward,cost,frame,nextRun,postEq,arithmetic⟩ := normal
  have memory : next.memory=stored.memory := by have h := congrArg PanSemStateFiniteExact.memory frame; exact h
  have domains : next.memaddrs=stored.memaddrs := by have h := congrArg PanSemStateFiniteExact.memaddrs frame; exact h
  have endian : next.be=stored.be := by have h := congrArg PanSemStateFiniteExact.be frame; exact h
  have nextHeap := Blob.HeapInput.of_fields stored next input pointer memory.symm domains.symm endian.symm prefixHeap
  have localOther (name : String) (different : ofString "nwd"≠ofString name) : next.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    rw [localsEq]
    exact bind_lookup_other source "nwd" name count different
  have countLocal : next.locals.lookup (ofString "nwd")=some (.val (.word count)) := by rw [localsEq]; exact bind_lookup_same _ _ _
  have completed := remaining_execute next input pointer cursor length withdrawals balances count nextHeap inside
    ((localOther "p" (by decide)).trans p) ((localOther "pl" (by decide)).trans pl) ((localOther "len" (by decide)).trans n)
    ((localOther "o_wd" (by decide)).trans w) ((localOther "o_bal" (by decide)).trans b) countLocal
    (domains.trans domain) pointerAligned cursorAligned pointerLower cursorAfter cursorRoom
  have equality := completed.1.symm.trans nextRun
  have answer := congrArg Prod.fst equality
  have finalClock := congrArg (fun output => output.2.clock) equality
  have clock : post.clock=next.clock := by rw [postEq]; exact finalClock.symm
  have innerEq : innerPost=emptyLocalsHOLFinite (applyFields next cursor (remainingFields input pointer length withdrawals balances count)) := (congrArg Prod.snd equality).symm
  have finalMemory : post.memory=fieldMemory stored.memory cursor (remainingFields input pointer length withdrawals balances count) := by
    rw [postEq,innerEq]
    change fieldMemory next.memory cursor (remainingFields input pointer length withdrawals balances count)=_
    rw [memory]
  have nextControl : WitnessRadix.BackingLayout.control next=WitnessRadix.BackingLayout.control source := by
    have h := congrArg WitnessRadix.BackingLayout.control frame
    exact h
  have control : WitnessRadix.BackingLayout.control post=WitnessRadix.BackingLayout.control source := by
    rw [postEq,innerEq]
    exact nextControl
  exact ⟨by rw [clock]; exact cost,Or.inr ⟨answer.symm,count,(arithmetic (by decide)).1,(arithmetic (by decide)).2,finalMemory,control⟩⟩


/-- Bound/outcome projection of the actual full suffix image. -/
theorem after_transactions_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor length records transactionCount withdrawals balances : BitVec 64)
    (heap : Blob.HeapInput source input pointer) (inside : 602≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))))
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word cursor)))
    (n : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (txs : source.locals.lookup (ofString "txs")=some (UDivMod.pairValue records transactionCount))
    (w : source.locals.lookup (ofString "o_wd")=some (.val (.word withdrawals)))
    (b : source.locals.lookup (ofString "o_bal")=some (.val (.word balances)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (cursorAligned : cursor.toNat%8=0)
    (pointerLower : 2701131776≤pointer.toNat)
    (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+136≤33806089496)
    (divisionCode : source.code.lookup (ofString "udivmod")=some (UDivMod.formals,UDivMod.body,UDivMod.returnShape))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (code : source.code.lookup (ofString "ssz_fixed_list_count")=some (FixedList.formals,FixedList.body,.one))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterTransactions=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤67 ∧
      ((∃ error : BitVec 64,(error=30#64 ∨ error=31#64) ∧ result=some (.exception (ofString "SszErr") (.val (.word error)))) ∨ result=some (.returned (.val (.word cursor)))) := by
  obtain ⟨cost,outcome⟩ := after_transactions_trace_image source post input pointer cursor length records transactionCount withdrawals balances heap inside p pl n txs w b domain pointerAligned cursorAligned pointerLower cursorAfter cursorRoom divisionCode failCode exceptionShape code result run notTimeout
  exact ⟨cost,outcome.imp id (fun normal => normal.1)⟩

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.after_transactions_trace

#print axioms InitECandidate.Solver.Input.Payload.after_transactions_trace_image
