import InitECandidate.Solver.Input.CurrentTable.Set.Update
import InitECandidate.Solver.Input.CurrentTable.CellGeometry

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

variable {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer value leaf : BitVec 64}
variable {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
variable {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}

theorem update_header (image : Image source table cap root next count valid bits left right keys ValueOf)
    (member : valid leaf) (field : Nat) (inside : field < 88) :
    (updated source table cap leaf value).memory (table+BitVec.ofNat 64 field) = source.memory (table+BitVec.ofNat 64 field) := by
  have away := image.geometry.header_away leaf (image.node_inside leaf member) 8 field (by decide) inside
  simp [updated,StoreWord.put,away]

/-- Leaf-value writes preserve every bit/child observation used by the
actual traversal. Internal child fields cannot alias this marked leaf. -/
theorem update_nodes (image : Image source table cap root next count valid bits left right keys ValueOf)
    (member : valid leaf) (marked : bits leaf = 256) :
    FindLeaf.Nodes (updated source table cap leaf value) (New.nodesPointer table cap) valid bits left right := by
  have leafInside := image.node_inside leaf member
  have away (node : BitVec 64) (live : valid node) (offset : Nat) (small : offset < 32) (different : offset ≠ 8) :
      FindLeaf.cell (New.nodesPointer table cap) node offset ≠ FindLeaf.cell (New.nodesPointer table cap) leaf 8 := by
    intro same
    have equal := cell_injective _ node leaf cap offset 8 image.geometry.nodes (image.node_inside node live) leafInside small (by decide) same
    exact different equal.2
  have leftAway (node : BitVec 64) (live : valid node) (internal : bits node < 256) :
      FindLeaf.cell (New.nodesPointer table cap) node 8 ≠ FindLeaf.cell (New.nodesPointer table cap) leaf 8 := by
    intro same
    have equal := (cell_injective _ node leaf cap 8 8 image.geometry.nodes (image.node_inside node live) leafInside (by decide) (by decide) same).1
    rw [equal,marked] at internal
    omega
  refine ⟨image.nodes.bitBound,image.nodes.bitMapped,?_,image.nodes.leftMapped,image.nodes.rightMapped,?_,?_,image.nodes.leftOrdered,image.nodes.rightOrdered⟩
  · intro node live
    simpa only [updated,StoreWord.put,if_neg (away node live 24 (by decide) (by decide))] using image.nodes.bitCell node live
  · intro node live internal
    simpa only [updated,StoreWord.put,if_neg (leftAway node live internal)] using image.nodes.leftCell node live internal
  · intro node live internal
    simpa only [updated,StoreWord.put,if_neg (away node live 16 (by decide) (by decide))] using image.nodes.rightCell node live internal

theorem update_keys (image : Image source table cap root next count valid bits left right keys ValueOf)
    (member : valid leaf) (node : BitVec 64) (live : valid node) (marked : bits node = 256) :
    FirstDiff.ByteView (updated source table cap leaf value) (slot (New.keysPointer table) node 32) (keys node) := by
  have view := image.leafKeys node live marked
  intro byte
  have before : (panByteAlignHOL (width:=64) (slot (New.keysPointer table) node 32+BitVec.ofNat 64 byte.val)).toNat <
      (FindLeaf.cell (New.nodesPointer table cap) leaf 8).toNat :=
    image.geometry.key_byte_before_node node leaf (image.node_inside node live) (image.node_inside leaf member) byte.val 8 byte.isLt (by decide)
  have away : panByteAlignHOL (width:=64) (slot (New.keysPointer table) node 32+BitVec.ofNat 64 byte.val) ≠
      FindLeaf.cell (New.nodesPointer table cap) leaf 8 := by
    intro same
    have equal := congrArg BitVec.toNat same
    omega
  change @panMemLoadByteHOL 64 _ (StoreWord.put source.memory (FindLeaf.cell (New.nodesPointer table cap) leaf 8) value)
    source.memaddrs (fun address => Classical.propDecidable (source.memaddrs address)) source.be
    (slot (New.keysPointer table) node 32+BitVec.ofNat 64 byte.val) = _
  rw [StoreWord.byte_away source _ value _ away]
  exact view byte

/-- Updating an existing leaf preserves the complete constructor-derived
image, with the actual new caller value satisfying its membership predicate. -/
theorem update_image (image : Image source table cap root next count valid bits left right keys ValueOf)
    (member : valid leaf) (marked : bits leaf = 256) (validValue : ValueOf value) :
    Image (updated source table cap leaf value) table cap root next count valid bits left right keys ValueOf := by
  have header := update_header (value:=value) image member
  refine ⟨image.geometry,image.aligned,image.domain,image.capLower,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    image.nextLower,image.nextBound,image.countBound,image.countNodes,image.empty,image.rootMember,image.validRange,
    update_nodes image member marked,image.routing,?_,?_⟩
  · simpa only [BitVec.add_zero] using (header 0 (by decide)).trans (by simpa only [BitVec.add_zero] using image.keyLength)
  · exact (header 8 (by decide)).trans image.stride
  · exact (header 16 (by decide)).trans image.capacity
  · exact (header 24 (by decide)).trans image.countCell
  · exact (header 32 (by decide)).trans image.keysCell
  · exact (header 40 (by decide)).trans image.nodesCell
  · exact (header 48 (by decide)).trans image.orderCell
  · exact (header 56 (by decide)).trans image.rootCell
  · exact (header 64 (by decide)).trans image.nextCell
  · exact (header 72 (by decide)).trans image.freeCell
  · exact (header 80 (by decide)).trans image.nodeCapacity
  · intro node live isLeaf
    exact update_keys image member node live isLeaf
  · intro node live isLeaf
    by_cases same : node = leaf
    · subst node
      exact ⟨value,by simp [updated,StoreWord.put],validValue⟩
    · obtain ⟨old,cell,validOld⟩ := image.leafValues node live isLeaf
      have away : FindLeaf.cell (New.nodesPointer table cap) node 8 ≠ FindLeaf.cell (New.nodesPointer table cap) leaf 8 := by
        intro equal
        exact same (cell_injective _ node leaf cap 8 8 image.geometry.nodes (image.node_inside node live) (image.node_inside leaf member)
          (by decide) (by decide) equal).1
      exact ⟨old,by simpa only [updated,StoreWord.put,if_neg away] using cell,validOld⟩

/-- Original input before the fresh table survives the real value write. -/
theorem update_before (image : Image source table cap root next count valid bits left right keys ValueOf)
    (member : valid leaf) (query : BitVec 64) (before : query.toNat < table.toNat) :
    (updated source table cap leaf value).memory query = source.memory query := by
  have after := image.geometry.cell_after_table leaf (image.node_inside leaf member) 8 (by decide)
  have away : query ≠ FindLeaf.cell (New.nodesPointer table cap) leaf 8 := by
    intro same
    have equal := congrArg BitVec.toNat same
    omega
  simp [updated,StoreWord.put,away]

/-- The actual normal true-comparison execution returns zero and retains
that full updated image in its same returned state. -/
theorem after_compare_one_returned (image : Image source table cap root next count valid bits left right keys ValueOf)
    (locals : LookupLocals source table pointer value leaf) (member : valid leaf) (marked : bits leaf = 256) (validValue : ValueOf value)
    (eqCell : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "eq") = some (.val (.word 1#64)))
    (post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterCompare = (some (.returned returned),post)) :
    returned = .val (.word 0#64) ∧ Image post table cap root next count valid bits left right keys ValueOf := by
  rw [after_compare_one image locals member eqCell] at normal
  have observed := congrArg Prod.fst normal
  have endpoint := congrArg Prod.snd normal
  dsimp only at endpoint
  have answer : .val (.word 0#64) = returned := by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using observed
  refine ⟨answer.symm,?_⟩
  rw [←endpoint]
  exact (update_image image member marked validValue).of_frame rfl

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.update_nodes
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.update_keys
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.update_image
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.update_before
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.after_compare_one_returned
