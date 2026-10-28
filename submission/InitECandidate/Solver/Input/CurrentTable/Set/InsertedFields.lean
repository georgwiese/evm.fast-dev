import InitECandidate.Solver.Input.CurrentTable.Set.InsertContext
import InitECandidate.Solver.Input.CurrentTable.Set.SpliceNodeFrame

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix

def insertedState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent pointer value : BitVec 64)
    (next count difference : Nat) (query : KeyBits.Key) (left : BitVec 64 → BitVec 64) :=
  spliceResult (freshModel source table cap pointer value next count difference) table cap node parent
    (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) (left parent) query difference

def insertedRoot (root parent : BitVec 64) (next : Nat) := if parent = 0#64 then BitVec.ofNat 64 (next+1) else root

variable {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value node parent : BitVec 64}
variable {next count difference : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
variable {keys : BitVec 64 → KeyBits.Key} {query : KeyBits.Key} {ValueOf : BitVec 64 → Prop}

theorem inserted_metadata (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node parent pointer value : BitVec 64)
    (next count difference : Nat) (query : KeyBits.Key) (left : BitVec 64 → BitVec 64) :
    MemoryMetadata.erase (insertedState source table cap node parent pointer value next count difference query left) = MemoryMetadata.erase source := by
  rw [insertedState,splice_metadata,fresh_metadata]

theorem inserted_header (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf)
    (field : Nat) (small : field < 88) (notCount : field ≠ 24) (notRoot : field ≠ 56) (notNext : field ≠ 64) :
    (insertedState source table cap node parent pointer value next count difference query left).memory (table+BitVec.ofNat 64 field) =
      source.memory (table+BitVec.ofNat 64 field) := by
  obtain ⟨leafInside,internalInside,posInside⟩ := fresh_slots data.image data.available
  rw [insertedState,splice_header _ table cap node parent _ _ _ query difference data.image.geometry data.node_inside data.parent_inside leafInside internalInside field small notRoot]
  exact fresh_header data.image data.available field small notCount notNext

theorem inserted_count (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf) :
    (insertedState source table cap node parent pointer value next count difference query left).memory (table+24#64) = .word (BitVec.ofNat 64 (count+1)) := by
  obtain ⟨leafInside,internalInside,posInside⟩ := fresh_slots data.image data.available
  rw [insertedState,splice_header _ table cap node parent _ _ _ query difference data.image.geometry data.node_inside data.parent_inside leafInside internalInside 24 (by decide) (by decide)]
  exact fresh_count data.image data.available

theorem inserted_next (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf) :
    (insertedState source table cap node parent pointer value next count difference query left).memory (table+64#64) = .word (BitVec.ofNat 64 (next+2)) := by
  obtain ⟨leafInside,internalInside,posInside⟩ := fresh_slots data.image data.available
  rw [insertedState,splice_header _ table cap node parent _ _ _ query difference data.image.geometry data.node_inside data.parent_inside leafInside internalInside 64 (by decide) (by decide)]
  exact fresh_next data.image data.available

theorem inserted_root (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf) :
    (insertedState source table cap node parent pointer value next count difference query left).memory (table+56#64) = .word (insertedRoot root parent next) := by
  obtain ⟨leafInside,internalInside,posInside⟩ := fresh_slots data.image data.available
  rw [insertedState,splice_root _ table cap node parent _ _ _ query difference data.image.geometry data.node_inside data.parent_inside leafInside internalInside]
  by_cases zero : parent = 0#64
  · simp only [insertedRoot,if_pos zero]
  · rw [if_neg zero,fresh_header data.image data.available 56 (by decide) (by decide) (by decide)]
    simp only [insertedRoot,if_neg zero]
    exact data.image.rootCell

theorem inserted_bit (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf)
    (index : BitVec 64) (member : Splice.valid valid (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) index) :
    (insertedState source table cap node parent pointer value next count difference query left).memory (FindLeaf.cell (New.nodesPointer table cap) index 24) =
      .word (BitVec.ofNat 64 (Splice.bits bits (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) difference index)) := by
  obtain ⟨leafInside,internalInside,posInside⟩ := fresh_slots data.image data.available
  rw [insertedState,splice_bit _ table cap node parent _ _ _ index query difference data.image.geometry data.node_inside data.parent_inside leafInside internalInside (data.valid_inside index member)]
  rcases member with old | rfl | rfl
  · rw [fresh_old_node data.image data.available index old 24 (by decide),data.fresh.old_bits old]
    exact data.image.nodes.bitCell index old
  · simp only [Splice.bits,↓reduceIte]
    exact (fresh_leaf_cells data.image data.available).2
  · simp only [Splice.bits,if_neg (Ne.symm data.fresh.distinct),↓reduceIte]
    exact fresh_internal_cells data.image data.available

theorem inserted_bit_bound (data : InsertContext source table cap root pointer value node parent next count difference valid bits left right keys query ValueOf)
    (index : BitVec 64) (member : Splice.valid valid (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) index) :
    Splice.bits bits (BitVec.ofNat 64 next) (BitVec.ofNat 64 (next+1)) difference index ≤ 256 := by
  rcases member with old | rfl | rfl
  · rw [data.fresh.old_bits old]
    exact data.image.nodes.bitBound index old
  · simp [Splice.bits]
  · simp only [Splice.bits,if_neg (Ne.symm data.fresh.distinct),↓reduceIte]
    have := data.fresh.inside
    omega

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.inserted_header
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.inserted_root
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.inserted_bit
