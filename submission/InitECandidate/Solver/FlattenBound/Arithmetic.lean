import InitECandidate.Solver.FlattenBound.Common

/-! Numerical obligations for branch, call and loop composition. Every clock
and syntax-size premise is explicit; these lemmas do not assume executions. -/
namespace InitECandidate.Solver.FlattenBound
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

theorem four_le_budget {width : Nat} [NeZero width] (limit : Nat) (p : HolProg width)
    (initial final : Nat) : 4 ≤ budget limit p initial final := by
  have := nodes_positive p
  unfold budget
  omega

theorem budget_branch_left {width : Nat} [NeZero width] (limit : Nat)
    (cmp : HolCmp) (reg : Nat) (ri : HolRegImm width) (p q : HolProg width)
    (initial final : Nat) :
    2 + budget limit p initial final ≤ budget limit (.ite cmp reg ri p q) initial final := by
  simp only [budget, nodes]
  omega

theorem budget_branch_right {width : Nat} [NeZero width] (limit : Nat)
    (cmp : HolCmp) (reg : Nat) (ri : HolRegImm width) (p q : HolProg width)
    (initial final : Nat) :
    2 + budget limit q initial final ≤ budget limit (.ite cmp reg ri p q) initial final := by
  simp only [budget, nodes]
  omega

theorem budget_enter {width : Nat} [NeZero width] (limit : Nat)
    (body current : HolProg width) (initial final cost : Nat)
    (smallBody : nodes body ≤ limit) (positive : initial ≠ 0)
    (clock : final ≤ initial - 1)
    (bounded : cost ≤ budget limit body (initial - 1) final) :
    cost + 3 ≤ budget limit current initial final := by
  have spent : initial - final = (initial - 1 - final) + 1 := by omega
  have := nodes_positive current
  simp only [budget, spent, Nat.mul_add, Nat.mul_one] at *
  omega

theorem budget_loop {width : Nat} [NeZero width] (limit : Nat)
    (body : HolProg width) (initial middle final first second : Nat)
    (smallBody : nodes body ≤ limit) (firstClock : middle ≤ initial)
    (positive : middle ≠ 0) (secondClock : final ≤ middle - 1)
    (firstBound : first ≤ budget limit body initial middle)
    (secondBound : second ≤ budget limit (.loop body) (middle - 1) final) :
    first + second + 1 ≤ budget limit (.loop body) initial final := by
  have spent : initial - final = (initial - middle) + (middle - 1 - final) + 1 := by omega
  simp only [budget, nodes, spent, Nat.mul_add, Nat.mul_one] at *
  omega

end InitECandidate.Solver.FlattenBound
#print axioms InitECandidate.Solver.FlattenBound.budget_enter
#print axioms InitECandidate.Solver.FlattenBound.budget_loop
