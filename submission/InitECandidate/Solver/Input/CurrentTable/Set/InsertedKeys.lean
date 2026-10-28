import InitECandidate.Solver.Input.CurrentTable.Set.InsertedFields
import InitECandidate.Solver.Input.CurrentTable.Set.SpliceKeys

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix

variable {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value node parent : BitVec 64}
variable {next count difference : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
variable {keys : BitVec 64 → KeyBits.Key} {query : KeyBits.Key} {ValueOf : BitVec 64 → Prop}

private theorem finish_key (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf)
    (index : BitVec 64) (inside : index.toNat ≤ cap.toNat) (key : KeyBits.Key)
    (view : FirstDiff.ByteView (freshModel source table cap pointer value next count difference) (slot (New.keysPointer table) index 32) key) :
    FirstDiff.ByteView (insertedState source table cap node parent pointer value next count difference query left) (slot (New.keysPointer table) index 32) key := by
  obtain ⟨leafInside,internalInside,posInside⟩ := fresh_slots data.image data.available
  exact splice_key _ table cap node parent _ _ _ index query key difference data.image.geometry data.node_inside data.parent_inside leafInside internalInside inside view

/-- Every genuine leaf in the new physical image retains its actual key,
including the new query leaf and all older leaves. -/
theorem inserted_key (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf)
    (index : BitVec 64) (member : Splice.valid valid (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) index)
    (marked : Splice.bits bits (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) difference index = 256) :
    FirstDiff.ByteView (insertedState source table cap node parent pointer value next count difference query left) (slot (New.keysPointer table) index 32)
      (Splice.keys keys (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) node query index) := by
  rcases member with old | rfl | rfl
  · rw [data.fresh.old_bits old] at marked
    rw [data.fresh.old_keys old]
    exact finish_key data index (data.image.node_inside index old) (keys index) (fresh_old_key data.image data.available index old marked)
  · simp only [Splice.keys,↓reduceIte]
    have inside := (fresh_slots data.image data.available).1
    exact finish_key data _ inside query (fresh_leaf_key data.image data.available query data.little data.aligned data.beforeTable data.view)
  · simp only [Splice.bits,if_neg (Ne.symm data.fresh.distinct),↓reduceIte] at marked
    have := data.fresh.inside
    omega

private theorem finish_value (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf)
    (index : BitVec 64) (inside : index.toNat ≤ cap.toNat) (notInternal : index ≠ BitVec.ofNat 64 (next+1)) (notParent : index ≠ parent) :
    (insertedState source table cap node parent pointer value next count difference query left).memory (FindLeaf.cell (New.nodesPointer table cap) index 8) =
      (freshModel source table cap pointer value next count difference).memory (FindLeaf.cell (New.nodesPointer table cap) index 8) := by
  obtain ⟨leafInside,internalInside,posInside⟩ := fresh_slots data.image data.available
  exact splice_leaf_value _ table cap node parent _ _ _ index query difference data.image.geometry data.node_inside data.parent_inside leafInside internalInside inside notInternal notParent

/-- The reached witness-value membership predicate survives fresh insertion
at every old leaf and holds for the actual newly supplied caller value. -/
theorem inserted_values (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf)
    (index : BitVec 64) (member : Splice.valid valid (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) index)
    (marked : Splice.bits bits (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) difference index = 256) :
    ∃ answer,(insertedState source table cap node parent pointer value next count difference query left).memory
      (FindLeaf.cell (New.nodesPointer table cap) index 8) = .word answer ∧ ValueOf answer := by
  rcases member with old | rfl | rfl
  · rw [data.fresh.old_bits old] at marked
    obtain ⟨answer,cell,validAnswer⟩ := data.image.leafValues index old marked
    have kept := finish_value data index (data.image.node_inside index old) (data.fresh.old_internal_ne old) (data.old_leaf_not_parent index old marked)
    exact ⟨answer,kept.trans ((fresh_old_node data.image data.available index old 8 (by decide)).trans cell),validAnswer⟩
  · have inside := (fresh_slots data.image data.available).1
    have kept := finish_value data _ inside data.fresh.distinct (Ne.symm data.parent_not_leaf)
    exact ⟨value,kept.trans (fresh_leaf_cells data.image data.available).1,data.valueMember⟩
  · simp only [Splice.bits,if_neg (Ne.symm data.fresh.distinct),↓reduceIte] at marked
    have := data.fresh.inside
    omega

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.inserted_key
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.inserted_values
