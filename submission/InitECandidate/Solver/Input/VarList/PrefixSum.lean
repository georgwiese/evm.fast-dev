import Lean.Elab.Tactic.Omega

namespace InitECandidate.Solver.Input.VarList

def sumPrefix (size : Nat→Nat) : Nat→Nat
  | 0=>0
  | index+1=>sumPrefix size index+size index
theorem prefix_telescope (offset size : Nat→Nat) (count : Nat)
    (ordered : ∀ index<count,offset index≤offset (index+1))
    (difference : ∀ index<count,size index=offset (index+1)-offset index) :
    ∀ index≤count,sumPrefix size index+offset 0=offset index := by
  intro index inside
  induction index with
  | zero=>simp [sumPrefix]
  | succ index ih=>
    have prev:=ih (by omega)
    have increasing:=ordered index (by omega)
    have delta:=difference index (by omega)
    simp only [sumPrefix]
    omega

theorem sum_prefix_mono (size : Nat→Nat) (lower upper : Nat) (inside : lower≤upper) :
    sumPrefix size lower≤sumPrefix size upper := by
  induction upper with
  | zero=>
    have eq : lower=0 := by omega
    subst lower
    exact Nat.le_refl _
  | succ upper ih=>
    by_cases same : lower=upper+1
    · rw [same]
      exact Nat.le_refl _
    · have previous:=ih (by omega)
      simp only [sumPrefix]
      omega

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.prefix_telescope
#print axioms InitECandidate.Solver.Input.VarList.sum_prefix_mono
