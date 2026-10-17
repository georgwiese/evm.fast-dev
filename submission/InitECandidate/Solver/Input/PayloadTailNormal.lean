import InitECandidate.Solver.Input.PayloadRemainingExecute
import InitECandidate.Solver.Input.PayloadWithdrawalsNormal

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A normal actual payload continuation after transaction splitting returns
its allocated payload and stores exactly the copied gas word at field88. -/
theorem after_transactions_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
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
    (enough : 67≤source.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source afterTransactions=(some (.returned value),post)) :
    value=.val (.word cursor) ∧ post.memory (cursor+88#64)=.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)) ∧
      Blob.HeapInput post input pointer ∧ source.clock-66≤post.clock ∧ post.clock≤source.clock ∧
      post.memory (cursor+56#64)=.word (BitVec.ofNat 64 ((balances-withdrawals).toNat/44)) := by
  classical
  obtain ⟨next,innerPost,count,paid,bound,localsEq,countBound,clock,frame,nextHeap,nextRun,postEq,arithmetic⟩:=withdrawals_normal source post input
    pointer cursor records transactionCount withdrawals balances heap pl txs w b domain pointerAligned cursorAligned pointerLower cursorAfter cursorRoom
    divisionCode failCode exceptionShape code enough value run
  have localOther : ∀ name : String,ofString "nwd"≠ofString name→next.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    intro name different
    rw [localsEq]
    exact bind_lookup_other source "nwd" name count different
  have countLocal : next.locals.lookup (ofString "nwd")=some (.val (.word count)) := by
    rw [localsEq]
    exact bind_lookup_same source "nwd" count
  have nextDomain:=congrArg PanSemStateFiniteExact.memaddrs frame
  change next.memaddrs=source.memaddrs at nextDomain
  have completed:=remaining_execute next input pointer cursor length withdrawals balances count nextHeap inside
    ((localOther "p" (by decide)).trans p) ((localOther "pl" (by decide)).trans pl) ((localOther "len" (by decide)).trans n)
    ((localOther "o_wd" (by decide)).trans w) ((localOther "o_bal" (by decide)).trans b) countLocal
    (nextDomain.trans domain) pointerAligned cursorAligned pointerLower cursorAfter cursorRoom
  let target:=emptyLocalsHOLFinite (applyFields next cursor (remainingFields input pointer length withdrawals balances count))
  have results:=completed.1.symm.trans nextRun
  have valueEq : value=.val (.word cursor) := by have eq:=congrArg Prod.fst results; cases eq; rfl
  have innerEq : innerPost=target:=(congrArg Prod.snd results).symm
  refine ⟨valueEq,?_,?_,?_,?_,?_⟩
  · rw [postEq,innerEq]
    exact completed.2.2.2.1
  · rw [postEq,innerEq]
    exact Blob.HeapInput.restore source target input pointer "nwd" completed.2.1
  · have finalClock : post.clock=next.clock := by rw [postEq,innerEq]; exact completed.2.2.1
    omega
  · have finalClock : post.clock=next.clock := by rw [postEq,innerEq]; exact completed.2.2.1
    omega
  · have countEq : count=BitVec.ofNat 64 ((balances-withdrawals).toNat/44) := by
      rw [←arithmetic.1]
      simp
    rw [postEq,innerEq,←countEq]
    exact completed.2.2.2.2

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.after_transactions_normal
