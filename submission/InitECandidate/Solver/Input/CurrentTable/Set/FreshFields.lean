import InitECandidate.Solver.Input.CurrentTable.Set.FreshInput
import InitECandidate.Solver.Input.CurrentTable.NewLeaf.Cells
import InitECandidate.Solver.Input.CurrentTable.NewLeaf.OldMemory

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix

variable {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value : BitVec 64}
variable {next count difference : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
variable {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}

theorem fresh_slots (image : Image source table cap root next count valid bits left right keys ValueOf) (available : next+1 ≤ cap.toNat) :
    (BitVec.ofNat 64 next).toNat ≤ cap.toNat ∧ (BitVec.ofNat 64 (next+1)).toNat ≤ cap.toNat ∧ (BitVec.ofNat 64 count).toNat ≤ cap.toNat := by
  have small := image.next_small
  have countSmall : count < 2^64 := by have := image.countBound; have := image.geometry.capacityBound; omega
  rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show next < 2^64 from by omega),Nat.mod_eq_of_lt (show next+1 < 2^64 from by omega),Nat.mod_eq_of_lt countSmall]
  exact ⟨by omega,available,image.countBound⟩

theorem fresh_distinct (image : Image source table cap root next count valid bits left right keys ValueOf) :
    BitVec.ofNat 64 next ≠ BitVec.ofNat 64 (next+1) := by
  have small := image.next_small
  intro same
  have equal := congrArg BitVec.toNat same
  rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show next < 2^64 from by omega),Nat.mod_eq_of_lt (show next+1 < 2^64 from by omega)] at equal
  omega

theorem fresh_metadata (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap pointer value : BitVec 64) (next count difference : Nat) :
    MemoryMetadata.erase (freshModel source table cap pointer value next count difference) = MemoryMetadata.erase source := by
  rw [freshModel,NewInternal.model_metadata,NewLeaf.model_metadata]

theorem fresh_header (image : Image source table cap root next count valid bits left right keys ValueOf) (available : next+1 ≤ cap.toNat)
    (field : Nat) (small : field < 88) (notCount : field ≠ 24) (notNext : field ≠ 64) :
    (freshModel source table cap pointer value next count difference).memory (table+BitVec.ofNat 64 field) = source.memory (table+BitVec.ofNat 64 field) := by
  obtain ⟨firstInside,secondInside,posInside⟩ := fresh_slots image available
  rw [freshModel,NewInternal.model_header _ table cap _ _ image.geometry secondInside field small notNext]
  exact NewLeaf.model_header source table cap _ _ pointer value image.geometry firstInside posInside field small notCount notNext

theorem fresh_count (image : Image source table cap root next count valid bits left right keys ValueOf) (available : next+1 ≤ cap.toNat) :
    (freshModel source table cap pointer value next count difference).memory (table+24#64) = .word (BitVec.ofNat 64 (count+1)) := by
  obtain ⟨firstInside,secondInside,posInside⟩ := fresh_slots image available
  rw [freshModel,NewInternal.model_header _ table cap _ _ image.geometry secondInside 24 (by decide) (by decide)]
  exact (NewLeaf.model_count source table cap _ _ pointer value).trans (by rw [BitVec.ofNat_add])

theorem fresh_next (image : Image source table cap root next count valid bits left right keys ValueOf) (available : next+1 ≤ cap.toNat) :
    (freshModel source table cap pointer value next count difference).memory (table+64#64) = .word (BitVec.ofNat 64 (next+2)) := by
  obtain ⟨firstInside,secondInside,posInside⟩ := fresh_slots image available
  rw [freshModel,NewInternal.model_next _ table cap _ _ image.geometry secondInside]
  congr 1
  rw [show next+2 = (next+1)+1 from by omega]
  simp only [BitVec.ofNat_add]

theorem fresh_old_node (image : Image source table cap root next count valid bits left right keys ValueOf) (available : next+1 ≤ cap.toNat)
    (index : BitVec 64) (member : valid index) (field : Nat) (small : field < 32) :
    (freshModel source table cap pointer value next count difference).memory (FindLeaf.cell (New.nodesPointer table cap) index field) =
      source.memory (FindLeaf.cell (New.nodesPointer table cap) index field) := by
  obtain ⟨firstInside,secondInside,posInside⟩ := fresh_slots image available
  have notLeaf : index ≠ BitVec.ofNat 64 next := by intro same; exact image.fresh_next (same ▸ member)
  have notInternal : index ≠ BitVec.ofNat 64 (next+1) := by intro same; exact image.fresh_next_succ (same ▸ member)
  rw [freshModel,NewInternal.model_old_node _ table cap _ _ index image.geometry secondInside (image.node_inside index member) notInternal field small]
  exact NewLeaf.model_old_node source table cap _ _ pointer value index image.geometry firstInside posInside (image.node_inside index member) notLeaf field small

theorem fresh_leaf_cells (image : Image source table cap root next count valid bits left right keys ValueOf) (available : next+1 ≤ cap.toNat) :
    (freshModel source table cap pointer value next count difference).memory (FindLeaf.cell (New.nodesPointer table cap) (BitVec.ofNat 64 next) 8) = .word value ∧
    (freshModel source table cap pointer value next count difference).memory (FindLeaf.cell (New.nodesPointer table cap) (BitVec.ofNat 64 next) 24) = .word 256#64 := by
  obtain ⟨firstInside,secondInside,posInside⟩ := fresh_slots image available
  have cells := NewLeaf.model_cells source table cap (BitVec.ofNat 64 next) (BitVec.ofNat 64 count) pointer value image.geometry firstInside posInside
  constructor
  · rw [freshModel,NewInternal.model_old_node _ table cap _ _ _ image.geometry secondInside firstInside (fresh_distinct image) 8 (by decide)]
    exact cells.2.1
  · rw [freshModel,NewInternal.model_old_node _ table cap _ _ _ image.geometry secondInside firstInside (fresh_distinct image) 24 (by decide)]
    exact cells.2.2.2.1

theorem fresh_internal_cells (image : Image source table cap root next count valid bits left right keys ValueOf) (available : next+1 ≤ cap.toNat) :
    (freshModel source table cap pointer value next count difference).memory (FindLeaf.cell (New.nodesPointer table cap) (BitVec.ofNat 64 (next+1)) 24) = .word (BitVec.ofNat 64 difference) := by
  obtain ⟨firstInside,secondInside,posInside⟩ := fresh_slots image available
  exact (NewInternal.model_cells _ table cap (BitVec.ofNat 64 (next+1)) (BitVec.ofNat 64 difference) image.geometry secondInside).2.2.2

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.fresh_header
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.fresh_old_node
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.fresh_leaf_cells
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.fresh_internal_cells
