import InitECandidate.Solver.MutableTable.TableRuntime.State
import InitECandidate.Solver.MutableTable.NaturalLayoutFrame

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack WitnessRadix NaturalLayout

def beforeSites : List Nat := [0, 8, 16, 24, 32, 40]
def afterSites : List Nat := [48, 56, 64]

theorem before_cells (kind : KeyHash.Kind) (start capacity : Nat) :
    (beforeWrites kind start capacity).map Prod.fst = beforeSites.map (cell (fresh kind start capacity) .header) := by
  simp [beforeWrites, beforeSites, cell, fresh, BitVec.ofNat_add]

theorem after_cells (kind : KeyHash.Kind) (start capacity : Nat) :
    (afterWrites kind start capacity).map Prod.fst = afterSites.map (cell (fresh kind start capacity) .header) := by
  simp [afterWrites, afterSites, cell, fresh, BitVec.ofNat_add]

theorem header_sites_nodup (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (sites : List Nat)
    (bounded : ∀ offset ∈ sites, offset < 72) (distinct : sites.Nodup) : (sites.map (cell plan .header)).Nodup := by
  induction sites with
  | nil => simp
  | cons offset rest ih =>
    have unique := List.nodup_cons.mp distinct
    apply List.nodup_cons.mpr
    refine ⟨?_, ih (fun other member => bounded other (List.mem_cons_of_mem offset member)) unique.2⟩
    intro member
    obtain ⟨other, otherMember, same⟩ := List.mem_map.mp member
    have equal : other = offset := by
      by_contra different
      exact cell_injective kind plan valid .header other offset
        (bounded other (List.mem_cons_of_mem offset otherMember)) (bounded offset (by simp)) different same
    exact unique.1 (equal ▸ otherMember)

theorem before_distinct (kind : KeyHash.Kind) (start capacity : Nat) (valid : Valid kind (fresh kind start capacity)) :
    ((beforeWrites kind start capacity).map Prod.fst).Nodup := by
  rw [before_cells]
  apply header_sites_nodup kind _ valid beforeSites _ (by decide)
  intro offset member
  simp only [beforeSites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem after_distinct (kind : KeyHash.Kind) (start capacity : Nat) (valid : Valid kind (fresh kind start capacity)) :
    ((afterWrites kind start capacity).map Prod.fst).Nodup := by
  rw [after_cells]
  apply header_sites_nodup kind _ valid afterSites _ (by decide)
  intro offset member
  simp only [afterSites, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide

theorem after_away (kind : KeyHash.Kind) (start capacity : Nat) (valid : Valid kind (fresh kind start capacity))
    (offset : Nat) (before : offset < 48) : cell (fresh kind start capacity) .header offset ∉ (afterWrites kind start capacity).map Prod.fst := by
  rw [after_cells]
  intro member
  obtain ⟨other, otherMember, same⟩ := List.mem_map.mp member
  have high : other < 72 := by
    simp only [afterSites, List.mem_cons, List.not_mem_nil, or_false] at otherMember
    rcases otherMember with rfl | rfl | rfl <;> decide
  have different : other ≠ offset := by
    simp only [afterSites, List.mem_cons, List.not_mem_nil, or_false] at otherMember
    omega
  exact cell_injective kind _ valid .header other offset high (by change offset < 72; omega) different same

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.before_cells
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.after_cells
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.header_sites_nodup
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.before_distinct
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.after_distinct
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.after_away
