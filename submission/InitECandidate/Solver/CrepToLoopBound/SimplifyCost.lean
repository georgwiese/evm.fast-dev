import InitECandidate.Solver.CrepToLoopBound.ProgramCost
import Flapjack.Pancake.CrepArith
import Flapjack.Pancake.Proofs.CrepArith.SimpProgCorrect

namespace InitECandidate.Solver.CrepToLoopBound
open Flapjack

private theorem mulConstCost {width : Nat} [NeZero width]
    (expression : CrepExpHOL width) (constant : BitVec width) :
    expCost (crepMulConstHOL expression constant) ≤ expCost expression := by
  unfold crepMulConstHOL
  split
  · simp [expCost]
  · split
    · exact Nat.le_refl _
    · split <;> simp [expCost, expsCost]

mutual
  theorem simplifyExpCost {width : Nat} [NeZero width] (expression : CrepExpHOL width) :
      expCost (crepSimpExpHOL expression) ≤ expCost expression := by
    cases expression with
    | load e | load32 e | loadByte e =>
      simpa only [crepSimpExpHOL, expCost] using simplifyExpCost e
    | op operator es =>
      simpa only [crepSimpExpHOL, expCost] using simplifyExpsCost es
    | cmp operator first second | shift operator first second =>
      have hfirst := simplifyExpCost first
      have hsecond := simplifyExpCost second
      simp only [crepSimpExpHOL, expCost]
      omega
    | crepOp operator es =>
      have ih := simplifyExpsCost es
      conv => lhs; arg 1; unfold crepSimpExpHOL
      simp only [expCost]
      split
      · rename_i mapped first second hes
        have hfirst := mulConstCost first
        have hsecond := mulConstCost second
        rw [hes] at ih
        simp only [expsCost, Nat.add_zero] at ih
        split
        · simp [expCost]
        · exact Nat.le_trans (hsecond _) (by omega)
        · exact Nat.le_trans (hfirst _) (by omega)
        · simpa only [expCost, hes, expsCost, Nat.add_zero] using ih
      · simpa only [expCost] using ih
    | _ => simp [crepSimpExpHOL, expCost]
  termination_by sizeOf expression

  theorem simplifyExpsCost {width : Nat} [NeZero width] (expressions : List (CrepExpHOL width)) :
      expsCost (expressions.map crepSimpExpHOL) ≤ expsCost expressions := by
    cases expressions with
    | nil => simp [expsCost]
    | cons expression expressions =>
      have first := simplifyExpCost expression
      have rest := simplifyExpsCost expressions
      simp only [List.map_cons, expsCost]
      omega
  termination_by sizeOf expressions
end

theorem simplifyCost {width : Nat} [NeZero width] (program : CrepProgHOL width) :
    cost (crepSimpProgHOL program) ≤ cost program := by
  cases program with
  | dec name value body =>
    have hv := simplifyExpCost value
    have hb := simplifyCost body
    simp only [crepSimpProgHOL, cost]
    omega
  | seq first second =>
    have hfirst := simplifyCost first
    have hsecond := simplifyCost second
    simp only [crepSimpProgHOL, cost]
    omega
  | ite condition first second =>
    have hc := simplifyExpCost condition
    have hfirst := simplifyCost first
    have hsecond := simplifyCost second
    simp only [crepSimpProgHOL, cost]
    omega
  | «while» condition body =>
    have hc := simplifyExpCost condition
    simp only [crepSimpProgHOL, cost]
    omega
  | assign _ value | storeGlob _ value | shMem _ _ value =>
    simpa only [crepSimpProgHOL, cost] using simplifyExpCost value
  | store first second | store32 first second | storeByte first second =>
    have hfirst := simplifyExpCost first
    have hsecond := simplifyExpCost second
    simp only [crepSimpProgHOL, cost]
    omega
  | call ret name args =>
    have argsCost := simplifyExpsCost args
    cases ret with
    | none => simpa only [crepSimpProgHOL, cost] using argsCost
    | some descriptor =>
      rcases descriptor with ⟨returns, handler⟩
      cases handler with
      | none => simpa only [crepSimpProgHOL, cost] using argsCost
      | some descriptor => rcases descriptor with ⟨eid, body⟩; simpa only [crepSimpProgHOL, cost] using argsCost
  | «return» values => simpa only [crepSimpProgHOL, cost] using simplifyExpsCost values
  | _ => simp [crepSimpProgHOL, cost]
termination_by sizeOf program

theorem simplifyCeiling {width : Nat} [NeZero width] (program : CrepProgHOL width) :
    ceiling (crepSimpProgHOL program) ≤ ceiling program := by
  have localCost := simplifyCost program
  cases program with
  | dec name value body =>
    have hb := simplifyCeiling body
    simp only [crepSimpProgHOL, ceiling]
    simp only [crepSimpProgHOL] at localCost
    omega
  | seq first second | ite _ first second =>
    have hfirst := simplifyCeiling first
    have hsecond := simplifyCeiling second
    simp only [crepSimpProgHOL, ceiling]
    simp only [crepSimpProgHOL] at localCost
    omega
  | «while» condition body =>
    have hb := simplifyCeiling body
    simp only [crepSimpProgHOL, ceiling]
    simp only [crepSimpProgHOL] at localCost
    omega
  | call ret name args =>
    cases ret with
    | none => simpa only [crepSimpProgHOL, ceiling, Nat.max_zero] using localCost
    | some descriptor =>
      rcases descriptor with ⟨returns, handler⟩
      cases handler with
      | none => simpa only [crepSimpProgHOL, ceiling, Nat.max_zero] using localCost
      | some descriptor =>
        rcases descriptor with ⟨eid, body⟩
        have hb := simplifyCeiling body
        simp only [crepSimpProgHOL, ceiling]
        simp only [crepSimpProgHOL] at localCost
        omega
  | _ => simpa only [crepSimpProgHOL, ceiling, Nat.max_zero] using localCost
termination_by sizeOf program

end InitECandidate.Solver.CrepToLoopBound
#print axioms InitECandidate.Solver.CrepToLoopBound.simplifyExpCost
#print axioms InitECandidate.Solver.CrepToLoopBound.simplifyExpsCost
#print axioms InitECandidate.Solver.CrepToLoopBound.simplifyCost
#print axioms InitECandidate.Solver.CrepToLoopBound.simplifyCeiling
