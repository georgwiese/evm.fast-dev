import InitECandidate.Solver.MutableTable.TableFamily
import InitECandidate.Solver.MutableTable.GrowRuntime.Amortized
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace InitECandidate.Solver.MutableTable.TableFamily
open scoped BigOperators

def Object.potential (object : Object) : Nat := GrowRuntime.growthPotential object.kind object.plan.capacity
def potential {ι : Type} [Fintype ι] (objects : ι → Object) : Nat := ∑ index, (objects index).potential

theorem potential_update_balance {ι : Type} [Fintype ι] [DecidableEq ι] (objects : ι → Object) (writer : ι) (next : Object) :
    potential (Function.update objects writer next) + (objects writer).potential = potential objects + next.potential := by
  have oldSplit := Finset.add_sum_erase Finset.univ (fun index => (objects index).potential) (Finset.mem_univ writer)
  have nextSplit := Finset.add_sum_erase Finset.univ (fun index => (Function.update objects writer next index).potential) (Finset.mem_univ writer)
  have rest : ∑ index ∈ Finset.univ.erase writer, (Function.update objects writer next index).potential =
      ∑ index ∈ Finset.univ.erase writer, (objects index).potential := by
    apply Finset.sum_congr rfl
    intro index inside
    rw [Function.update_of_ne (Finset.ne_of_mem_erase inside)]
  simp only [Function.update_self] at nextSplit
  rw [rest] at nextSplit
  change (objects writer).potential + _ = potential objects at oldSplit
  change next.potential + _ = potential (Function.update objects writer next) at nextSplit
  omega

/-- Charge one actual table mutation against the whole live family's
potential, so different rollback writers telescope in a single loop. -/
theorem amortized_update {ι : Type} [Fintype ι] [DecidableEq ι] (objects : ι → Object) (writer : ι) (next : Object)
    (paid price : Nat) (bound : paid + (objects writer).potential ≤ price + next.potential) :
    paid + potential objects ≤ price + potential (Function.update objects writer next) := by
  have balance := potential_update_balance objects writer next
  omega

theorem population_update {ι : Type} [DecidableEq ι] (objects : ι → Object) (writer : ι) (next : Object) (count : Nat)
    (bounded : ∀ index, (objects index).slots.length ≤ count) (step : next.slots.length ≤ (objects writer).slots.length + 1) :
    ∀ index, (Function.update objects writer next index).slots.length ≤ count + 1 := by
  intro index
  by_cases same : index = writer
  · subst index
    rw [Function.update_self]
    have old := bounded writer
    omega
  · rw [Function.update_of_ne same]
    have old := bounded index
    omega

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.potential_update_balance
#print axioms InitECandidate.Solver.MutableTable.TableFamily.amortized_update
#print axioms InitECandidate.Solver.MutableTable.TableFamily.population_update
