import InitECandidate.Solver.Input.RequestRootHashCall

namespace InitECandidate.Solver.Input.RequestRootHash

theorem body_price_components (data : Description) : bodyPrice data=PayloadHash.bodyPrice data.payload+RequestsHash.price data.requestCount+115*data.blobCount+24801 := by
  calc
    bodyPrice data=PayloadHash.bodyPrice data.payload+RequestsHash.price data.requestCount+115*data.blobCount+(1+1+1+24207+5+1+584+1) := by
      unfold bodyPrice pipelinePrice phases Phase.price
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
      ac_rfl
    _ = _ := rfl

/-- Collected original request-root body allowance, charging each actual
transaction byte/count and each actual request/blob count once. Source
clocks omit straight-line target instructions and are not the final K. -/
theorem body_price_formula (data : Description) : bodyPrice data=
    4*VarList.sumPrefix data.payload.transactionLength data.payload.transactionCount+24514*data.payload.transactionCount+732*data.payload.withdrawalCount+
      data.payload.extraLength/8+115*PackBytes.chunks data.payload.extraLength+data.payload.balanceLength/8+115*PackBytes.chunks data.payload.balanceLength+
      115*data.blobCount+1827*data.requestCount .deposit+988*data.requestCount .wdreq+1364*data.requestCount .cons+
      1652*data.requestCount .bdep+813*data.requestCount .bexit+271195 := by
  rw [body_price_components,PayloadHash.body_price_formula]
  unfold RequestsHash.price
  have constants : 100550+145844+24801=271195 := rfl
  rw [←constants]
  ac_rfl

end InitECandidate.Solver.Input.RequestRootHash
#print axioms InitECandidate.Solver.Input.RequestRootHash.body_price_components
#print axioms InitECandidate.Solver.Input.RequestRootHash.body_price_formula
