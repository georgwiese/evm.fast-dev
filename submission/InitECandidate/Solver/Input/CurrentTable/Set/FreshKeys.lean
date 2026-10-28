import InitECandidate.Solver.Input.CurrentTable.Set.FreshFields

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix

variable {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value : BitVec 64}
variable {next count difference : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
variable {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}

theorem fresh_leaf_key (image : Image source table cap root next count valid bits left right keys ValueOf) (available : next+1 ≤ cap.toNat)
    (query : KeyBits.Key) (little : source.be = false) (aligned : pointer.toNat%8 = 0)
    (before : pointer.toNat+32 ≤ table.toNat) (view : FirstDiff.ByteView source pointer query) :
    FirstDiff.ByteView (freshModel source table cap pointer value next count difference) (slot (New.keysPointer table) (BitVec.ofNat 64 next) 32) query := by
  obtain ⟨firstInside,secondInside,posInside⟩ := fresh_slots image available
  have fields := NewLeaf.fields_from_image query image (by omega) little aligned before view
  have copied := NewLeaf.model_key source table cap (BitVec.ofNat 64 next) (BitVec.ofNat 64 count) pointer value query fields before
  exact NewInternal.model_key _ table cap (BitVec.ofNat 64 (next+1)) (BitVec.ofNat 64 difference) (BitVec.ofNat 64 next) query image.geometry secondInside firstInside copied

theorem fresh_old_key (image : Image source table cap root next count valid bits left right keys ValueOf) (available : next+1 ≤ cap.toNat)
    (index : BitVec 64) (member : valid index) (marked : bits index = 256) :
    FirstDiff.ByteView (freshModel source table cap pointer value next count difference) (slot (New.keysPointer table) index 32) (keys index) := by
  obtain ⟨firstInside,secondInside,posInside⟩ := fresh_slots image available
  have notLeaf : index ≠ BitVec.ofNat 64 next := by intro same; exact image.fresh_next (same ▸ member)
  have copied := NewLeaf.model_old_key source table cap (BitVec.ofNat 64 next) (BitVec.ofNat 64 count) pointer value index (keys index)
    image.geometry firstInside posInside (image.node_inside index member) notLeaf (image.leafKeys index member marked)
  exact NewInternal.model_key _ table cap (BitVec.ofNat 64 (next+1)) (BitVec.ofNat 64 difference) index (keys index) image.geometry secondInside (image.node_inside index member) copied

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.fresh_leaf_key
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.fresh_old_key
