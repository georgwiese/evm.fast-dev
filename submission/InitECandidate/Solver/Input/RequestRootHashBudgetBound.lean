import InitECandidate.Solver.Input.MainRequestRootHashBudget

set_option maxRecDepth 1000000

namespace InitECandidate.Solver.Input.Main.RequestRootHashData

/-- Original packed-byte call/loop allowance is linear even at a partial
last chunk; no assumption about input contents or hash values is needed. -/
theorem packed_price_bound (length : Nat) : length/8+115*PackBytes.chunks length≤4*length+115 := by
  unfold PackBytes.chunks
  omega

/-- A uniform request-root source bound derived from the same shared byte
budget. The largest price per encoded byte is a zero-length transaction's
original four-byte offset entry; other data never pay another input maximum. -/
theorem byte_price_bound (data : RequestRootHash.Description) :
    RequestRootHash.bodyPrice data≤6129*(dataBytes data-622)+271425 := by
  have extra := packed_price_bound data.payload.extraLength
  have balance := packed_price_bound data.payload.balanceLength
  rw [RequestRootHash.body_price_formula]
  unfold dataBytes
  omega

theorem budget_price_bound (data : RequestRootHash.Description) (budget witness : Nat)
    (shared : dataBytes data+witness≤budget) : RequestRootHash.bodyPrice data≤6129*(budget-622)+271425 :=
  (byte_price_bound data).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 6129 (Nat.sub_le_sub_right (Nat.le_trans (Nat.le_add_right _ _) shared) 622)) 271425)

end InitECandidate.Solver.Input.Main.RequestRootHashData
#print axioms InitECandidate.Solver.Input.Main.RequestRootHashData.packed_price_bound
#print axioms InitECandidate.Solver.Input.Main.RequestRootHashData.byte_price_bound
#print axioms InitECandidate.Solver.Input.Main.RequestRootHashData.budget_price_bound
