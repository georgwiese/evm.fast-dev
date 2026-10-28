import InitECandidate.Solver.Input.CurrentTable.NewLeaf.Cells
import InitECandidate.Solver.Input.CurrentTable.FieldFrames
import InitECandidate.Solver.Input.CurrentTable.NewLeaf.ModelFields

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix

def firstState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap leaf pointer value : BitVec 64) :=
  New.putField (NewLeaf.model source table cap leaf 0#64 pointer value) table 56 leaf

/-- The real fresh-leaf writes followed by the original empty-branch root
store establish a full nonempty image, including physical key/value bytes. -/
theorem first_image {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap leaf pointer value : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop} (query : KeyBits.Key)
    (leafOne : leaf = 1#64)
    (image : Image source table cap 0#64 next count valid bits left right keys ValueOf)
    (fields : NewLeaf.Fields source table cap leaf 0#64 pointer query) (beforeTable : pointer.toNat+32 ≤ table.toNat)
    (validValue : ValueOf value) :
    Image (firstState source table cap leaf pointer value) table cap leaf 2 1 (fun node => node = leaf)
      (fun _ => 256) (fun _ => 0#64) (fun _ => 0#64) (fun _ => query) ValueOf := by
  let leafState := NewLeaf.model source table cap leaf 0#64 pointer value
  let finalState := firstState source table cap leaf pointer value
  have domain : finalState.memaddrs = source.memaddrs := by
    change (New.putField leafState table 56 leaf).memaddrs = _
    rw [putField_domain,NewLeaf.model_domain]
  have inside : leaf.toNat ≤ cap.toNat := fields.inside
  have zeroInside : (0#64 : BitVec 64).toNat ≤ cap.toNat := by change 0 ≤ cap.toNat; omega
  have header (offset : Nat) (small : offset < 88) (notCount : offset ≠ 24) (notRoot : offset ≠ 56) (notNext : offset ≠ 64) :
      finalState.memory (table+BitVec.ofNat 64 offset) = source.memory (table+BitVec.ofNat 64 offset) := by
    change (New.putField leafState table 56 leaf).memory _ = _
    rw [header_other leafState table leaf 56 offset image.geometry.table (by decide) small notRoot]
    exact NewLeaf.model_header source table cap leaf 0#64 pointer value image.geometry inside zeroInside offset small notCount notNext
  have cells := NewLeaf.model_cells source table cap leaf 0#64 pointer value image.geometry inside zeroInside
  have finalCell (offset : Nat) (small : offset < 32) :
      finalState.memory (FindLeaf.cell (New.nodesPointer table cap) leaf offset) = leafState.memory (FindLeaf.cell (New.nodesPointer table cap) leaf offset) :=
    header_node leafState table cap leaf leaf 56 offset image.geometry inside (by decide) small
  have nodeImage : FindLeaf.Nodes finalState (New.nodesPointer table cap) (fun node => node = leaf) (fun _ => 256) (fun _ => 0#64) (fun _ => 0#64) := by
    refine ⟨by intros; omega,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro node same
      subst node
      rw [domain]
      exact AllocatedBytes.word_mapped source (slot (New.nodesPointer table cap) leaf 32) 32 24 image.domain
        (image.geometry.node_slot leaf inside) (by decide)
        (slot_aligned _ leaf cap 32 image.geometry.nodes inside image.geometry.nodesAligned (by decide)) (by decide)
    · intro node same
      subst node
      exact (finalCell 24 (by decide)).trans cells.2.2.2.1
    all_goals intro node same active; omega
  have routing : Routing (fun node : BitVec 64 => node = leaf) (fun _ => 256) (fun _ => 0#64) (fun _ => 0#64) (fun _ => query) := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro node same
      rw [same,leafOne]
      decide
    all_goals intro node same active; omega
  refine ⟨image.geometry,image.aligned,domain.trans image.domain,image.capLower,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    by omega,by have := image.capLower; omega,by have := image.capLower; omega,by omega,by simp [leafOne],Or.inr rfl,?_,nodeImage,routing,?_,?_⟩
  · simpa only [BitVec.add_zero] using (header 0 (by decide) (by decide) (by decide) (by decide)).trans (by simpa only [BitVec.add_zero] using image.keyLength)
  · exact (header 8 (by decide) (by decide) (by decide) (by decide)).trans image.stride
  · exact (header 16 (by decide) (by decide) (by decide) (by decide)).trans image.capacity
  · change (New.putField leafState table 56 leaf).memory _ = _
    rw [header_other leafState table leaf 56 24 image.geometry.table (by decide) (by decide) (by decide)]
    exact NewLeaf.model_count source table cap leaf 0#64 pointer value
  · exact (header 32 (by decide) (by decide) (by decide) (by decide)).trans image.keysCell
  · exact (header 40 (by decide) (by decide) (by decide) (by decide)).trans image.nodesCell
  · exact (header 48 (by decide) (by decide) (by decide) (by decide)).trans image.orderCell
  · simp [finalState,firstState,New.putField,StoreWord.put]
  · change (New.putField leafState table 56 leaf).memory _ = _
    rw [header_other leafState table leaf 56 64 image.geometry.table (by decide) (by decide) (by decide)]
    exact (NewLeaf.model_next source table cap leaf 0#64 pointer value image.geometry inside zeroInside).trans (by rw [leafOne]; rfl)
  · exact (header 72 (by decide) (by decide) (by decide) (by decide)).trans image.freeCell
  · exact (header 80 (by decide) (by decide) (by decide) (by decide)).trans image.nodeCapacity
  · intro node
    constructor
    · intro same
      rw [same,leafOne]
      decide
    · intro range
      apply BitVec.eq_of_toNat_eq
      rw [leafOne]
      change node.toNat = 1
      omega
  · intro node same marked
    subst node
    exact header_key leafState table cap leaf leaf 56 query image.geometry inside (by decide) (NewLeaf.model_key source table cap leaf 0#64 pointer value query fields beforeTable)
  · intro node same marked
    subst node
    exact ⟨value,(finalCell 8 (by decide)).trans cells.2.1,validValue⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.first_image
