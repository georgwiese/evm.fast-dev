import InitECandidate.Solver.Input.CurrentTable.Set.InsertedFields
import InitECandidate.Solver.Input.CurrentTable.Set.SpliceEdges

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix

variable {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value node parent : BitVec 64}
variable {next count difference : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
variable {keys : BitVec 64 → KeyBits.Key} {query : KeyBits.Key} {ValueOf : BitVec 64 → Prop}

private theorem left_test (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf)
    (index : BitVec 64) (member : valid index) :
    (parent ≠ 0#64 ∧ index = parent ∧ left parent = node) ↔ (index = parent ∧ left index = node) := by
  constructor
  · intro condition
    exact ⟨condition.2.1,by rw [condition.2.1]; exact condition.2.2⟩
  · intro condition
    refine ⟨?_,condition.1,?_⟩
    · intro zero
      exact data.image.routing.nonzero index member (condition.1.trans zero)
    · rw [←condition.1]; exact condition.2

private theorem right_test (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf)
    (index : BitVec 64) (member : valid index) :
    (parent ≠ 0#64 ∧ index = parent ∧ left parent ≠ node) ↔ (index = parent ∧ right index = node) := by
  constructor
  · intro condition
    exact ⟨condition.2.1,by rw [condition.2.1]; exact (data.right_selected condition.1).mpr condition.2.2⟩
  · intro condition
    have nonzero : parent ≠ 0#64 := by intro zero; exact data.image.routing.nonzero index member (condition.1.trans zero)
    refine ⟨nonzero,condition.1,(data.right_selected nonzero).mp ?_⟩
    rw [←condition.1]; exact condition.2

theorem inserted_left (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf)
    (index : BitVec 64) (member : Splice.valid valid (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) index)
    (active : Splice.bits bits (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) difference index < 256) :
    (insertedState source table cap node parent pointer value next count difference query left).memory (FindLeaf.cell (New.nodesPointer table cap) index 8) =
      .word (Splice.side left (BitVec.ofNat 64 (next+1)) parent node (Splice.choice (BitVec.ofNat 64 next) node query difference false) index) := by
  obtain ⟨leafInside,internalInside,posInside⟩ := fresh_slots data.image data.available
  rcases member with old | rfl | rfl
  · rw [data.fresh.old_bits old] at active
    rw [insertedState,splice_old_left _ table cap node parent _ _ _ index query difference data.image.geometry data.node_inside data.parent_inside leafInside internalInside
      (data.image.node_inside index old) (data.fresh.old_internal_ne old),fresh_old_node data.image data.available index old 8 (by decide),data.image.nodes.leftCell index old active]
    rw [Splice.side,if_neg (data.fresh.old_internal_ne old)]
    by_cases patch : index = parent ∧ left index = node
    · rw [if_pos patch,if_pos ((left_test data index old).mpr patch)]
    · rw [if_neg patch,if_neg (by intro condition; exact patch ((left_test data index old).mp condition))]
  · simp only [Splice.bits,↓reduceIte] at active
    omega
  · have cells := (splice_new_children (freshModel source table cap pointer value next count difference) table cap node parent (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) (left parent) query difference
      data.image.geometry data.parent_inside internalInside (Ne.symm data.parent_not_internal)).1
    cases digit : KeyBits.bit query difference <;>
      simpa [insertedState,Splice.side,Splice.choice,digit] using cells

theorem inserted_right (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf)
    (index : BitVec 64) (member : Splice.valid valid (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) index)
    (active : Splice.bits bits (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) difference index < 256) :
    (insertedState source table cap node parent pointer value next count difference query left).memory (FindLeaf.cell (New.nodesPointer table cap) index 16) =
      .word (Splice.side right (BitVec.ofNat 64 (next+1)) parent node (Splice.choice (BitVec.ofNat 64 next) node query difference true) index) := by
  obtain ⟨leafInside,internalInside,posInside⟩ := fresh_slots data.image data.available
  rcases member with old | rfl | rfl
  · rw [data.fresh.old_bits old] at active
    rw [insertedState,splice_old_right _ table cap node parent _ _ _ index query difference data.image.geometry data.node_inside data.parent_inside leafInside internalInside
      (data.image.node_inside index old) (data.fresh.old_internal_ne old),fresh_old_node data.image data.available index old 16 (by decide),data.image.nodes.rightCell index old active]
    rw [Splice.side,if_neg (data.fresh.old_internal_ne old)]
    by_cases patch : index = parent ∧ right index = node
    · rw [if_pos patch,if_pos ((right_test data index old).mpr patch)]
    · rw [if_neg patch,if_neg (by intro condition; exact patch ((right_test data index old).mp condition))]
  · simp only [Splice.bits,↓reduceIte] at active
    omega
  · have cells := (splice_new_children (freshModel source table cap pointer value next count difference) table cap node parent (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) (left parent) query difference
      data.image.geometry data.parent_inside internalInside (Ne.symm data.parent_not_internal)).2
    cases digit : KeyBits.bit query difference <;>
      simpa [insertedState,Splice.side,Splice.choice,digit] using cells

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.inserted_left
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.inserted_right
