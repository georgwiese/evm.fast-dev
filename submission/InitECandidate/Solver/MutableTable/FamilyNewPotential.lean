import InitECandidate.Solver.MutableTable.FamilyPotential
import InitECandidate.Solver.MutableTable.FamilyExtend
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option

namespace InitECandidate.Solver.MutableTable.TableFamily
open scoped BigOperators

theorem potential_extend {ι : Type} [Fintype ι] (objects : ι → Object) (fresh : Object) :
    potential (extend objects fresh) = potential objects + fresh.potential := by
  simp [potential,Fintype.sum_option,extend,Nat.add_comm]

/-- One real new table and one changed old table. All other old identities
retain their exact objects, so the full-family potential charges each once. -/
theorem potential_option_balance {ι : Type} [Fintype ι] [DecidableEq ι]
    (objects : ι → Object) (next : Option ι → Object) (writer : ι)
    (others : ∀ reader,reader ≠ writer → next (some reader) = objects reader) :
    potential next + (objects writer).potential = potential objects + (next (some writer)).potential + (next none).potential := by
  have old : (fun index => next (some index)) = Function.update objects writer (next (some writer)) := by
    funext index
    by_cases same : index = writer
    · subst index; rw [Function.update_self]
    · rw [Function.update_of_ne same,others index same]
  have split : potential next = (next none).potential + potential (fun index => next (some index)) := by
    simp only [potential,Fintype.sum_option]
  have balance := potential_update_balance objects writer (next (some writer))
  rw [← old] at balance
  omega

end InitECandidate.Solver.MutableTable.TableFamily

#print axioms InitECandidate.Solver.MutableTable.TableFamily.potential_extend
#print axioms InitECandidate.Solver.MutableTable.TableFamily.potential_option_balance
