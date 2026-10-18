import InitECandidate.Solver.MutableTable.FamilyFloorFrame
import InitECandidate.Solver.GasBudget.Frame

namespace InitECandidate.Solver.GasBudget
open Flapjack PanSemStateFiniteExact MutableTable

theorem word_below_tables {ι : Type} {objects next : ι → TableFamily.Object}
    {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (saved : TableFamily.FloorFrame objects next source target) (pointer : BitVec 64) (offset cut : Nat)
    (floors : ∀ index, cut ≤ (objects index).floor)
    (before : pointer.toNat + offset < cut) (cutSmall : cut < 2 ^ 64) :
    target.memory (pointer + BitVec.ofNat 64 offset) = source.memory (pointer + BitVec.ofNat 64 offset) := by
  apply saved.below cut floors
  have offsetSmall : offset < 2 ^ 64 := by omega
  have sumSmall : pointer.toNat + (BitVec.ofNat 64 offset).toNat < 2 ^ 64 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt offsetSmall]
    omega
  rw [BitVec.toNat_add_of_lt sumSmall, BitVec.toNat_ofNat, Nat.mod_eq_of_lt offsetSmall]
  exact before

/-- A table/journal mutation frame retains the active regular-gas ledger
when its three real words precede every persistent table lifetime floor.
The arena split and reachable table floors remain caller obligations. -/
theorem regularBudget_of_table_frame {ι : Type} {objects next : ι → TableFamily.Object}
    {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (saved : TableFamily.FloorFrame objects next source target) (frame : BitVec 64)
    (before : ∀ offset ∈ ([64, 184, 192] : List Nat), ∀ index, (frame + BitVec.ofNat 64 offset).toNat < (objects index).floor) :
    regularBudget target.memory frame = regularBudget source.memory frame := by
  simp only [regularBudget, wordAt, saved.words _ (before 64 (by simp)), saved.words _ (before 184 (by simp)), saved.words _ (before 192 (by simp))]

/-- One common arena split supplies all three ledger-cell premises without
requiring a particular table index or an invented abstract gas state. -/
theorem regularBudget_below_tables {ι : Type} {objects next : ι → TableFamily.Object}
    {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (saved : TableFamily.FloorFrame objects next source target) (frame : BitVec 64) (cut : Nat)
    (floors : ∀ index, cut ≤ (objects index).floor)
    (frameSmall : frame.toNat + 200 ≤ cut) (cutSmall : cut < 2 ^ 64) :
    regularBudget target.memory frame = regularBudget source.memory frame := by
  apply regularBudget_of_table_frame saved frame
  intro offset member index
  have offsetBound : offset ≤ 192 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> omega
  have sumSmall : frame.toNat + (BitVec.ofNat 64 offset).toNat < 2 ^ 64 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [BitVec.toNat_add_of_lt sumSmall, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have afterFrame := floors index
  omega

end InitECandidate.Solver.GasBudget

#print axioms InitECandidate.Solver.GasBudget.regularBudget_of_table_frame
#print axioms InitECandidate.Solver.GasBudget.word_below_tables
#print axioms InitECandidate.Solver.GasBudget.regularBudget_below_tables
