import InitECandidate.Solver.MutableTable.FamilyPotential

namespace InitECandidate.Solver.MutableTable.TableFamily
open scoped BigOperators

/-- Two actual growth sites can be charged against the entire live family.
Other mutations may change contents while retaining their allocation potential. -/
theorem potential_two_balance {ι : Type} [Fintype ι] [DecidableEq ι]
    (objects next : ι → Object) (first second : ι) (different : first ≠ second)
    (others : ∀ index,index ≠ first → index ≠ second → (next index).potential = (objects index).potential) :
    potential next + (objects first).potential + (objects second).potential =
      potential objects + (next first).potential + (next second).potential := by
  let changed := Function.update (Function.update objects first (next first)) second (next second)
  have same : potential next = potential changed := by
    apply Finset.sum_congr rfl
    intro index _
    by_cases atFirst : index = first
    · subst index
      simp [changed,Function.update_of_ne different]
    · by_cases atSecond : index = second
      · subst index
        simp [changed]
      · simpa only [changed,Function.update_of_ne atSecond,Function.update_of_ne atFirst] using others index atFirst atSecond
  have step1 := potential_update_balance objects first (next first)
  have step2 := potential_update_balance (Function.update objects first (next first)) second (next second)
  rw [Function.update_of_ne different.symm] at step2
  change potential changed + (objects second).potential = _ at step2
  omega

theorem amortized_two {ι : Type} [Fintype ι] [DecidableEq ι]
    (objects next : ι → Object) (first second : ι) (different : first ≠ second)
    (others : ∀ index,index ≠ first → index ≠ second → (next index).potential = (objects index).potential)
    (paid price : Nat)
    (bound : paid + (objects first).potential + (objects second).potential ≤ price + (next first).potential + (next second).potential) :
    paid + potential objects ≤ price + potential next := by
  have balance := potential_two_balance objects next first second different others
  omega

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.potential_two_balance
#print axioms InitECandidate.Solver.MutableTable.TableFamily.amortized_two
