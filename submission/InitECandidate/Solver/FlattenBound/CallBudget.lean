import InitECandidate.Solver.FlattenBound.Arithmetic

namespace InitECandidate.Solver.FlattenBound
open Flapjack Flapjack.Compiler.Backend.StackLang

theorem nodes_return_le {width : Nat} [NeZero width] (p : HolProg width)
    (link l1 l2 : Nat) (dest : Nat ⊕ Nat) (handler : Option (HolProg width × Nat × Nat)) :
    nodes p ≤ nodes (.call (some (p, link, l1, l2)) dest handler) := by
  rcases handler with _ | ⟨body, a, b⟩ <;> simp only [nodes] <;> omega

theorem nodes_handler_le {width : Nat} [NeZero width]
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Nat ⊕ Nat)
    (p : HolProg width) (l1 l2 : Nat) :
    nodes p ≤ nodes (.call ret dest (some (p, l1, l2))) := by
  rcases ret with _ | ⟨body, link, a, b⟩ <;> simp only [nodes] <;> omega

theorem budget_continue {width : Nat} [NeZero width] (limit : Nat)
    (body continuation current : HolProg width) (initial middle final first second : Nat)
    (smallBody : nodes body ≤ limit) (subprogram : nodes continuation ≤ nodes current)
    (positive : initial ≠ 0) (firstClock : middle ≤ initial - 1) (secondClock : final ≤ middle)
    (firstBound : first ≤ budget limit body (initial - 1) middle)
    (secondBound : second ≤ budget limit continuation middle final) :
    first + second + 3 ≤ budget limit current initial final := by
  have spent : initial - final = (initial - 1 - middle) + (middle - final) + 1 := by omega
  simp only [budget, spent, Nat.mul_add, Nat.mul_one] at *
  omega

end InitECandidate.Solver.FlattenBound
#print axioms InitECandidate.Solver.FlattenBound.budget_continue
