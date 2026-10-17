import InitECandidate.Solver.MutableTable.TableRuntime.Call
import InitECandidate.Solver.MutableTable.TableRuntime.Cells
import InitECandidate.Solver.MutableTable.NaturalLayoutBounds

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

theorem sites_away (kind : KeyHash.Kind) (start capacity : Nat) (valid : Valid kind (fresh kind start capacity))
    (query : BitVec 64) (away : query.toNat < start ∨ freshEnd kind start capacity ≤ query.toNat)
    (sites : List Nat) (bounds : ∀ offset ∈ sites, offset < 72) :
    query ∉ sites.map (cell (fresh kind start capacity) .header) := by
  intro member
  obtain ⟨offset, site, same⟩ := List.mem_map.mp member
  exact fresh_cell_away kind start capacity valid query away .header offset (bounds offset site) same.symm

/-- Actual used clearing preserves every word outside the whole allocation,
including the four-byte constructor case and either byte order. -/
theorem clear_away (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) (query : BitVec 64)
    (away : query.toNat < start ∨ freshEnd kind start capacity ≤ query.toNat) :
    clearMemory memory be kind start capacity query = memory query := by
  have roundBound := (rounded_bounds capacity).1
  by_cases four : capacity = 4
  · simp only [clearMemory, if_pos four]
    apply Zero.memoryByte_away
    intro offset inside
    rw [Nat.zero_add]
    change query ≠ panByteAlignHOL (width := 64) (byteAddress (cell (fresh kind start capacity) .used 0) offset)
    rw [offset_cell, byte_cell kind _ valid .used offset (by change offset < rounded capacity; omega)]
    exact fresh_cell_away kind start capacity valid query away .used _ (by change 8 * (offset / 8) < rounded capacity; omega)
  · simp only [clearMemory, if_neg four]
    apply Zero.final_memory_away
    intro offset inside
    change query ≠ byteAddress (cell (fresh kind start capacity) .used 0) offset
    rw [offset_cell]
    exact fresh_cell_away kind start capacity valid query away .used offset (by change offset < rounded capacity; omega)

/-- The entire real constructor memory frame, not merely a helper frame:
all prior and later records outside its exact reservation are untouched. -/
theorem result_away (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) (query : BitVec 64)
    (away : query.toNat < start ∨ freshEnd kind start capacity ≤ query.toNat) :
    resultMemory memory be kind start capacity query = memory query := by
  have before : query ∉ (beforeWrites kind start capacity).map Prod.fst := by
    rw [before_cells]
    apply sites_away kind start capacity valid query away beforeSites
    intro offset member
    simp only [beforeSites, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have after : query ∉ (afterWrites kind start capacity).map Prod.fst := by
    rw [after_cells]
    apply sites_away kind start capacity valid query away afterSites
    intro offset member
    simp only [afterSites, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  rw [resultMemory, WordWrites.write_away _ _ _ after, clear_away _ be kind start capacity valid query away,
    WordWrites.write_away _ _ _ before]

theorem caller_memory_away {F : Type} (source : PanSemStateFiniteExact 64 F) (name : String) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) (query : BitVec 64)
    (away : query.toNat < start ∨ freshEnd kind start capacity ≤ query.toNat) :
    (callState source name kind start capacity).memory query = source.memory query :=
  result_away source.memory source.be kind start capacity valid query away

/-- Exact persistent reservation, including the used-array alignment gap. -/
theorem reservation (kind : KeyHash.Kind) (start capacity : Nat) :
    freshEnd kind start capacity = start + 72 + (stride kind + 24) * capacity + rounded capacity := by
  simp only [freshEnd, Nat.add_mul]
  omega

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.sites_away
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.clear_away
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.result_away
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.caller_memory_away
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.reservation
