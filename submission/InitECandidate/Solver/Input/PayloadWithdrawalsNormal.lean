import InitECandidate.Solver.Input.PayloadTransactionStores

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Both actual transaction tuple-field stores, then the actual withdrawal
count call and caller resumption. All copied input and payload fields outside
those two stores preserve; the real fixed-list call pays at most66 clocks. -/
theorem withdrawals_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor records transactionCount withdrawals balances : BitVec 64) (heap : Blob.HeapInput source input pointer)
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word cursor)))
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
    ∃ next innerPost count paid,paid≤66 ∧
      next.locals=source.locals.update (ofString "nwd",.val (.word count)) ∧ count.toNat≤9223372036854775807 ∧
      next.clock=source.clock-paid ∧
      UDivMod.frozen next=UDivMod.frozen (transactionFieldsStored source cursor records transactionCount) ∧
      Blob.HeapInput next input pointer ∧
      evaluateHOLFiniteState next afterWithdrawals=(some (.returned value),innerPost) ∧ post=restore source "nwd" innerPost := by
  obtain ⟨prefixRun,prefixHeap⟩:=transaction_stores source input pointer cursor records transactionCount heap pl txs domain pointerAligned cursorAligned
    pointerLower cursorAfter cursorRoom
  let stored:=transactionFieldsStored source cursor records transactionCount
  have args:=withdrawal_arguments stored withdrawals balances w b
  have tailRun : evaluateHOLFiniteState stored withdrawalCall=(some (.returned value),post):=prefixRun.symm.trans run
  rw [transactions_shape.2.2.2] at tailRun
  obtain ⟨next,innerPost,count,paid,bound,localsEq,countBound,clock,frame,nextRun,postEq⟩:=FixedList.caller_normal stored post
    (balances-withdrawals) 44#64 9223372036854775807#64 (by decide) divisionCode failCode exceptionShape code
    "nwd" withdrawalArguments afterWithdrawals args enough value tailRun
  have memoryEq:=congrArg PanSemStateFiniteExact.memory frame
  change next.memory=stored.memory at memoryEq
  have domainEq:=congrArg PanSemStateFiniteExact.memaddrs frame
  change next.memaddrs=stored.memaddrs at domainEq
  have endianEq:=congrArg PanSemStateFiniteExact.be frame
  change next.be=stored.be at endianEq
  exact ⟨next,innerPost,count,paid,bound,localsEq,countBound,clock,frame,
    Blob.HeapInput.of_fields stored next input pointer memoryEq.symm domainEq.symm endianEq.symm prefixHeap,nextRun,postEq⟩

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.withdrawals_normal
