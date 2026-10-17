import InitECandidate.Solver.GasBudget.CallGasCall

namespace InitECandidate.Solver.GasBudget
open Flapjack PanSemStateFiniteExact

/-- The actual regular-counter subtraction may remove forwarded gas including
the stipend. Up-front value fees must already fund the stipend part. -/
theorem forward_counter_number (words : U256Zero.Quad) (requested left used : BitVec 64)
    (leftFits : left.toNat+2300<2^64) (budgetFits : left.toNat+used.toNat<2^64)
    (funded : (CallGas.stipend words).toNat≤used.toNat) :
    ((used+CallGas.capped requested left)-(CallGas.capped requested left+CallGas.stipend words)).toNat=
      used.toNat-(CallGas.stipend words).toNat ∧
    (left-CallGas.capped requested left).toNat+
      ((used+CallGas.capped requested left)-(CallGas.capped requested left+CallGas.stipend words)).toNat+
      (CallGas.capped requested left+CallGas.stipend words).toNat=left.toNat+used.toNat := by
  have capBound:=(CallGas.capped_number requested left).2
  have debitWord : CallGas.capped requested left≤left:=capBound
  have forwardNat:=(CallGas.forwarded_number words requested left leftFits).2
  have usedSum : (used+CallGas.capped requested left).toNat=used.toNat+(CallGas.capped requested left).toNat:=
    BitVec.toNat_add_of_lt (by omega)
  have forwardedAffordable : CallGas.capped requested left+CallGas.stipend words≤used+CallGas.capped requested left := by
    change (CallGas.capped requested left+CallGas.stipend words).toNat≤(used+CallGas.capped requested left).toNat
    rw [forwardNat,usedSum]
    omega
  rw [BitVec.toNat_sub_of_le forwardedAffordable,usedSum,BitVec.toNat_sub_of_le debitWord,forwardNat]
  omega

/-- Subtract a legitimately forwarded amount from the real used-counter cell.
All other regular-budget cells are preserved by the literal word write. -/
theorem used_debit_budget (memory : Memory) (frame used forwarded : BitVec 64)
    (stored : memory (frame+184#64)=.word used) (affordable : forwarded≤used) :
    regularBudget (WitnessRadix.StoreWord.put memory (frame+184#64) (used-forwarded)) frame+forwarded.toNat=
      regularBudget memory frame := by
  have gasAway:=offsets_ne frame 64#64 184#64 (by decide)
  have spillAway:=offsets_ne frame 192#64 184#64 (by decide)
  simp only [regularBudget,wordAt,WitnessRadix.StoreWord.put,if_neg gasAway,if_neg spillAway,if_pos rfl,
    stored,WitnessRadix.MemoryBytes.wordBits]
  change ((wordAt memory (frame+64#64)).toNat+(used-forwarded).toNat+(wordAt memory (frame+192#64)).toNat)+forwarded.toNat=
    (wordAt memory (frame+64#64)).toNat+used.toNat+(wordAt memory (frame+192#64)).toNat
  have bound : forwarded.toNat≤used.toNat:=affordable
  rw [BitVec.toNat_sub_of_le affordable]
  omega

theorem stipend_funded_by_value_fee (usedBefore usedAfter charged : Nat) (words : U256Zero.Quad)
    (actualCredit : usedAfter=usedBefore+charged) (valueFee : 11300≤charged) :
    (CallGas.stipend words).toNat≤usedAfter := by
  have small:=CallGas.stipend_bound words
  omega

end InitECandidate.Solver.GasBudget

#print axioms InitECandidate.Solver.GasBudget.forward_counter_number
#print axioms InitECandidate.Solver.GasBudget.used_debit_budget
#print axioms InitECandidate.Solver.GasBudget.stipend_funded_by_value_fee
