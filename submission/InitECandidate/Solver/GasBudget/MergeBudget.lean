import InitECandidate.Solver.GasBudget.NestedDecay

namespace InitECandidate.Solver.GasBudget.MergeBudget

/-- A counting model for arbitrary call forests, including sequential children.
It is not a runtime trace or a claim about actual table contents. -/
inductive Forest where
  | produced (events : Nat)
  | join (first second : Forest)
  | child (inside : Forest)

def production : Forest→Nat
  | .produced n=>n
  | .join a b=>production a+production b
  | .child t=>production t

def depth : Forest→Nat
  | .produced _=>0
  | .join a b=>max (depth a) (depth b)
  | .child t=>depth t+1

/-- Each production event is counted once for every enclosing child edge. -/
def propagation : Forest→Nat
  | .produced _=>0
  | .join a b=>propagation a+propagation b
  | .child t=>propagation t+production t

theorem propagation_bound (forest : Forest) : propagation forest≤depth forest*production forest := by
  induction forest with
  | produced n=>simp [propagation,depth]
  | join a b ha hb=>
    have da : depth a≤max (depth a) (depth b):=Nat.le_max_left _ _
    have db : depth b≤max (depth a) (depth b):=Nat.le_max_right _ _
    have aBound:=(ha.trans (Nat.mul_le_mul_right (production a) da))
    have bBound:=(hb.trans (Nat.mul_le_mul_right (production b) db))
    simp only [propagation,depth,production]
    rw [Nat.mul_add]
    omega
  | child inside ih=>
    simp only [propagation,depth,production]
    rw [Nat.add_mul,Nat.one_mul]
    omega

def productions (roots : List Forest) : Nat := (roots.map production).sum
def propagationWork (maxKeys : Nat) (roots : List Forest) : Nat :=
  (roots.map (fun root=>(maxKeys+1)*propagation root)).sum

/-- Uniform occupancy and depth bound, with aggregate production rather than
sum of declared root gas. Repeated children and arbitrary forests are covered
by this counting model. Runtime event/merge coupling remains a separate duty. -/
theorem work_bound (roots : List Forest) (maxKeys maxDepth : Nat)
    (depths : ∀ root∈roots,depth root≤maxDepth) :
    propagationWork maxKeys roots≤(maxKeys+1)*maxDepth*productions roots := by
  induction roots with
  | nil=>simp [propagationWork,productions]
  | cons root rest ih=>
    have rootBound:=(propagation_bound root).trans
      (Nat.mul_le_mul_right (production root) (depths root (by simp)))
    have weighted:=Nat.mul_le_mul_left (maxKeys+1) rootBound
    have tail:=ih (by intro r member;exact depths r (by simp [member]))
    simp only [propagationWork,productions,List.map_cons,List.sum_cons] at tail ⊢
    rw [Nat.mul_add]
    rw [← Nat.mul_assoc] at weighted
    omega

/-- Conditional delete-set propagation envelope. The premises must be supplied
by actual regular-gas, production, table occupancy and call-depth invariants. -/
theorem paid_work_bound (roots : List Forest) (maxKeys maxDepth totalGas price : Nat)
    (positive : 0<price) (paid : productions roots*price≤totalGas)
    (depths : ∀ root∈roots,depth root≤maxDepth) :
    propagationWork maxKeys roots≤(maxKeys+1)*maxDepth*(totalGas/price) := by
  have produced : productions roots≤totalGas/price:=(Nat.le_div_iff_mul_le positive).mpr paid
  exact (work_bound roots maxKeys maxDepth depths).trans (Nat.mul_le_mul_left _ produced)

/-- Exact literal relaxation only; no global380M gas premise is proved here. -/
theorem scenario_380M (roots : List Forest)
    (paid : productions roots*5000≤380000000)
    (depths : ∀ root∈roots,depth root≤538) :
    propagationWork 6000 roots≤245368888000 := by
  have bound:=paid_work_bound roots 6000 538 380000000 5000 (by decide) paid depths
  exact bound

end InitECandidate.Solver.GasBudget.MergeBudget

#print axioms InitECandidate.Solver.GasBudget.MergeBudget.propagation_bound
#print axioms InitECandidate.Solver.GasBudget.MergeBudget.work_bound
#print axioms InitECandidate.Solver.GasBudget.MergeBudget.paid_work_bound
#print axioms InitECandidate.Solver.GasBudget.MergeBudget.scenario_380M
