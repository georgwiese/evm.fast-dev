import InitECandidate.Solver.GasBudget.ValueFeeSites

namespace InitECandidate.Solver.GasBudget.NestedDecay
open Flapjack

def capNat (gas : Nat) : Nat := gas-gas/64
def next (budget : Nat) : Nat := capNat (budget-100)

theorem cap_mono (small large : Nat) (ordered : small≤large) : capNat small≤capNat large := by
  unfold capNat
  omega

theorem stipend_compensation (gas : Nat) : capNat gas+2300≤capNat (gas+11300) := by
  unfold capNat
  omega

/-- A paid100 minimum access fee yields one uniform child bound. Nonzero
stipends require the actual additional11300 value fee, which more than funds
the2300 credit. These are execution-entry premises, not a whole trace claim. -/
theorem child_bound (parent available fee bonus child : Nat)
    (within : available+fee≤parent) (access : 100≤fee)
    (bonusBound : bonus≤2300) (value : bonus≠0→11400≤fee)
    (forwarded : child≤capNat available+bonus) : child≤next parent := by
  by_cases zero : bonus=0
  · have bound:=cap_mono available (parent-100) (by omega)
    unfold next
    omega
  · have feeBound:=value zero
    have bound:=cap_mono (available+11300) (parent-100) (by omega)
    have compensated:=stipend_compensation available
    unfold next
    omega

theorem calculator_child_bound (words : U256Zero.Quad) (requested left : BitVec 64) (parent fee : Nat)
    (leftFits : left.toNat+2300<2^64) (within : left.toNat+fee≤parent) (access : 100≤fee)
    (value : (CallGas.stipend words).toNat≠0→11400≤fee) :
    (CallGas.capped requested left+CallGas.stipend words).toNat≤next parent := by
  have forwarded:=(CallGas.forwarded_number words requested left leftFits).2
  have cappedBound : (CallGas.capped requested left).toNat≤capNat left.toNat := by
    rw [(CallGas.capped_number requested left).1]
    change min requested.toNat (CallGas.cap left).toNat≤left.toNat-left.toNat/64
    rw [(CallGas.cap_number left).1]
    exact Nat.min_le_right _ _
  exact child_bound parent left.toNat fee (CallGas.stipend words).toNat _ within access (CallGas.stipend_bound words) value (by rw [forwarded]; omega)

/-- Shifted gas potential contracts by63/64 on every affordable call edge. -/
theorem affine_edge (parent child : Nat) (affordable : 100≤parent) (bound : child≤next parent) :
    64*(child+6237)≤63*(parent+6237) := by
  unfold next capNat at bound
  omega

theorem geometric_chain (budget : Nat→Nat) (depth : Nat)
    (edges : ∀ index<depth,64*(budget (index+1)+6237)≤63*(budget index+6237)) :
    64^depth*(budget depth+6237)≤63^depth*(budget 0+6237) := by
  induction depth with
  | zero=>simp
  | succ depth ih=>
    have prior:=ih (by intro index inside; exact edges index (by omega))
    have edge:=edges depth (by omega)
    calc
      64^(depth+1)*(budget (depth+1)+6237)=64^depth*(64*(budget (depth+1)+6237)) := by rw [Nat.pow_succ,Nat.mul_assoc]
      _ ≤64^depth*(63*(budget depth+6237)):=Nat.mul_le_mul_left _ edge
      _ =63*(64^depth*(budget depth+6237)):=Nat.mul_left_comm _ _ _
      _ ≤63*(63^depth*(budget 0+6237)):=Nat.mul_le_mul_left _ prior
      _ =63^(depth+1)*(budget 0+6237) := by rw [Nat.pow_succ,Nat.mul_comm (63^depth) 63,Nat.mul_assoc]

set_option maxRecDepth 10000 in
theorem depth_literal : 63^539*(30000000+6237)<64^539*6237 := by decide

/-- Conditional nesting bound for the actual30M maximum root gas scenario.
The runtime must still supply every edge's fee and budget invariant. -/
theorem chain_depth (budget : Nat→Nat) (depth : Nat) (root : budget 0≤30000000)
    (edges : ∀ index<depth,100≤budget index ∧ budget (index+1)≤next (budget index)) : depth≤538 := by
  by_contra outside
  have prefixEdges : ∀ index<539,64*(budget (index+1)+6237)≤63*(budget index+6237) := by
    intro index inside
    have edge:=edges index (by omega)
    exact affine_edge _ _ edge.1 edge.2
  have geometric:=geometric_chain budget 539 prefixEdges
  have lower : 64^539*6237≤64^539*(budget 539+6237):=Nat.mul_le_mul_left _ (by omega)
  have upper : 63^539*(budget 0+6237)≤63^539*(30000000+6237):=Nat.mul_le_mul_left _ (by omega)
  have impossible:=(lower.trans geometric).trans upper
  exact Nat.not_lt_of_ge impossible depth_literal

end InitECandidate.Solver.GasBudget.NestedDecay

#print axioms InitECandidate.Solver.GasBudget.NestedDecay.cap_mono
#print axioms InitECandidate.Solver.GasBudget.NestedDecay.stipend_compensation
#print axioms InitECandidate.Solver.GasBudget.NestedDecay.child_bound
#print axioms InitECandidate.Solver.GasBudget.NestedDecay.calculator_child_bound
#print axioms InitECandidate.Solver.GasBudget.NestedDecay.affine_edge
#print axioms InitECandidate.Solver.GasBudget.NestedDecay.geometric_chain
#print axioms InitECandidate.Solver.GasBudget.NestedDecay.depth_literal
#print axioms InitECandidate.Solver.GasBudget.NestedDecay.chain_depth
