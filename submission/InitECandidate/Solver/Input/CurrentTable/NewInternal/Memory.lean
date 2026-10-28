import InitECandidate.Solver.Input.CurrentTable.NewInternal.Call
import InitECandidate.Solver.Input.CurrentTable.NodeFrames

namespace InitECandidate.Solver.Input.CurrentTable.NewInternal
open Flapjack PanSemStateFiniteExact WitnessRadix

def model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node bit : BitVec 64) :=
  stored (New.putField source table 64 (node+1#64)) (New.nodesPointer table cap) node bit

theorem model_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node bit : BitVec 64)
    (frame : LocalEffects.erase target = LocalEffects.erase source) :
    LocalEffects.erase (model target table cap node bit) = LocalEffects.erase (model source table cap node bit) := by
  exact node_frame _ _ _ node bit 24 (node_frame _ _ _ node 0#64 16
    (node_frame _ _ _ node 0#64 8 (node_frame _ _ _ node 0#64 0 (header_frame source target table (node+1#64) 64 frame))))

theorem stored_header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node bit : BitVec 64)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (field : Nat) (small : field < 88) :
    (stored source (New.nodesPointer table cap) node bit).memory (table+BitVec.ofNat 64 field) = source.memory (table+BitVec.ofNat 64 field) := by
  rw [stored,node_header _ table cap node bit 24 field geometry inside (by decide) small,
    node_header _ table cap node 0#64 16 field geometry inside (by decide) small,
    node_header _ table cap node 0#64 8 field geometry inside (by decide) small,
    node_header _ table cap node 0#64 0 field geometry inside (by decide) small]

theorem model_header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node bit : BitVec 64)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (field : Nat) (small : field < 88) (different : field ≠ 64) :
    (model source table cap node bit).memory (table+BitVec.ofNat 64 field) = source.memory (table+BitVec.ofNat 64 field) := by
  rw [model,stored_header _ table cap node bit geometry inside field small]
  exact header_other source table (node+1#64) 64 field geometry.table (by decide) small different

theorem model_next (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node bit : BitVec 64)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) :
    (model source table cap node bit).memory (table+64#64) = .word (node+1#64) := by
  rw [model,stored_header _ table cap node bit geometry inside 64 (by decide)]
  simp [New.putField,StoreWord.put]

theorem model_key (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node bit keyNode : BitVec 64) (key : KeyBits.Key)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (keyInside : keyNode.toNat ≤ cap.toNat)
    (view : FirstDiff.ByteView source (slot (New.keysPointer table) keyNode 32) key) :
    FirstDiff.ByteView (model source table cap node bit) (slot (New.keysPointer table) keyNode 32) key := by
  have allocated := header_key source table cap (node+1#64) keyNode 64 key geometry keyInside (by decide) view
  exact node_key _ table cap node keyNode bit 24 key geometry inside keyInside (by decide)
    (node_key _ table cap node keyNode 0#64 16 key geometry inside keyInside (by decide)
      (node_key _ table cap node keyNode 0#64 8 key geometry inside keyInside (by decide)
        (node_key _ table cap node keyNode 0#64 0 key geometry inside keyInside (by decide) allocated)))

theorem model_old_node (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node bit other : BitVec 64)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (otherInside : other.toNat ≤ cap.toNat)
    (different : other ≠ node) (field : Nat) (small : field < 32) :
    (model source table cap node bit).memory (FindLeaf.cell (New.nodesPointer table cap) other field) =
      source.memory (FindLeaf.cell (New.nodesPointer table cap) other field) := by
  rw [model,stored,
    node_other _ table cap node other bit 24 field geometry inside otherInside (by decide) small (Or.inl different),
    node_other _ table cap node other 0#64 16 field geometry inside otherInside (by decide) small (Or.inl different),
    node_other _ table cap node other 0#64 8 field geometry inside otherInside (by decide) small (Or.inl different),
    node_other _ table cap node other 0#64 0 field geometry inside otherInside (by decide) small (Or.inl different)]
  exact header_node source table cap (node+1#64) other 64 field geometry otherInside (by decide) small

theorem model_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node bit : BitVec 64)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) :
    (model source table cap node bit).memory (FindLeaf.cell (New.nodesPointer table cap) node 0) = .word 0#64 ∧
    (model source table cap node bit).memory (FindLeaf.cell (New.nodesPointer table cap) node 8) = .word 0#64 ∧
    (model source table cap node bit).memory (FindLeaf.cell (New.nodesPointer table cap) node 16) = .word 0#64 ∧
    (model source table cap node bit).memory (FindLeaf.cell (New.nodesPointer table cap) node 24) = .word bit := by
  have apart (x y : Nat) (xInside : x < 32) (yInside : y < 32) (different : x ≠ y) :
      FindLeaf.cell (New.nodesPointer table cap) node x ≠ FindLeaf.cell (New.nodesPointer table cap) node y := by
    intro same
    exact different (cell_injective _ node node cap x y geometry.nodes inside inside xInside yInside same).2
  simp only [model,stored,putNode,StoreWord.put,↓reduceIte,
    if_neg (apart 0 8 (by decide) (by decide) (by decide)),if_neg (apart 0 16 (by decide) (by decide) (by decide)),
    if_neg (apart 0 24 (by decide) (by decide) (by decide)),if_neg (apart 8 16 (by decide) (by decide) (by decide)),
    if_neg (apart 8 24 (by decide) (by decide) (by decide)),if_neg (apart 16 24 (by decide) (by decide) (by decide)),and_self]

end InitECandidate.Solver.Input.CurrentTable.NewInternal

#print axioms InitECandidate.Solver.Input.CurrentTable.NewInternal.model_header
#print axioms InitECandidate.Solver.Input.CurrentTable.NewInternal.model_next
#print axioms InitECandidate.Solver.Input.CurrentTable.NewInternal.model_key
#print axioms InitECandidate.Solver.Input.CurrentTable.NewInternal.model_old_node
#print axioms InitECandidate.Solver.Input.CurrentTable.NewInternal.model_cells
