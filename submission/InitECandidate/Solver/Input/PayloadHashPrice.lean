import InitECandidate.Solver.Input.PayloadHashCall

namespace InitECandidate.Solver.Input.PayloadHash

/-- Collected allowance for the unchanged complete payload body. This is a
source call/loop clock count, before straight-line target-cost transport. -/
theorem body_price_formula (data : Description) : bodyPrice data=
    4*VarList.sumPrefix data.transactionLength data.transactionCount+24514*data.transactionCount+732*data.withdrawalCount+
      data.extraLength/8+115*PackBytes.chunks data.extraLength+data.balanceLength/8+115*PackBytes.chunks data.balanceLength+100550 := by
  calc
    bodyPrice data=4*VarList.sumPrefix data.transactionLength data.transactionCount+(24399*data.transactionCount+115*data.transactionCount)+732*data.withdrawalCount+
        data.extraLength/8+115*PackBytes.chunks data.extraLength+data.balanceLength/8+115*PackBytes.chunks data.balanceLength+
        (1+1+1260+149+10+1+1+24207+1+24283+50636) := by
      unfold bodyPrice StaticPrefix.price StaticPrefix.extraSuffixPrice StaticPrefix.middlePrice Extra.price TransactionScope.price
        TransactionSuffix.loopSuffixPrice TransactionSuffix.afterLoopPrice TransactionSuffix.afterListPrice TransactionSuffix.withdrawalPrice BalancePhase.price
      ac_rfl
    _ = _ := by rw [←Nat.add_mul]

end InitECandidate.Solver.Input.PayloadHash
#print axioms InitECandidate.Solver.Input.PayloadHash.body_price_formula
