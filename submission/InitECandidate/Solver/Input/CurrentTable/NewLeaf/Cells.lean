import InitECandidate.Solver.Input.CurrentTable.NewLeaf.Header
import Mathlib.Data.List.Nodup

namespace InitECandidate.Solver.Input.CurrentTable.NewLeaf
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem node_before_order (table cap node pos : BitVec 64) (geometry : New.Geometry table cap)
    (inside : node.toNat ≤ cap.toNat) (posInside : pos.toNat ≤ cap.toNat) (offset : Nat) (small : offset < 32) :
    (FindLeaf.cell (New.nodesPointer table cap) node offset).toNat < (slot (New.orderPointer table cap) pos 8).toNat := by
  rw [cell_number _ node cap offset geometry.nodes inside small,slot_number _ pos cap 8 geometry.order posInside]
  have := geometry.nodesBefore
  omega

theorem stored_writes_distinct (table cap node pos value : BitVec 64) (geometry : New.Geometry table cap)
    (inside : node.toNat ≤ cap.toNat) (posInside : pos.toNat ≤ cap.toNat) :
    ((storedWrites table cap node pos value).map Prod.fst).Nodup := by
  have apart (x y : Nat) (xInside : x < 32) (yInside : y < 32) (different : x ≠ y) :
      FindLeaf.cell (New.nodesPointer table cap) node x ≠ FindLeaf.cell (New.nodesPointer table cap) node y := by
    intro same
    exact different (cell_injective _ node node cap x y geometry.nodes inside inside xInside yInside same).2
  have orderAway (offset : Nat) (small : offset < 32) :
      FindLeaf.cell (New.nodesPointer table cap) node offset ≠ slot (New.orderPointer table cap) pos 8 := by
    have before := node_before_order table cap node pos geometry inside posInside offset small
    intro same
    have equal := congrArg BitVec.toNat same
    omega
  have headerAway (offset : Nat) (small : offset < 32) :
      FindLeaf.cell (New.nodesPointer table cap) node offset ≠ table+24#64 :=
    Ne.symm (geometry.header_away node inside offset 24 small (by decide))
  have orderHeader : slot (New.orderPointer table cap) pos 8 ≠ table+24#64 :=
    Ne.symm (order_header_away table cap pos geometry posInside 24 (by decide))
  simp [storedWrites,List.nodup_cons,
    apart 0 8 (by decide) (by decide) (by decide),apart 0 16 (by decide) (by decide) (by decide),
    apart 0 24 (by decide) (by decide) (by decide),apart 8 16 (by decide) (by decide) (by decide),
    apart 8 24 (by decide) (by decide) (by decide),apart 16 24 (by decide) (by decide) (by decide),
    orderAway 0 (by decide),orderAway 8 (by decide),orderAway 16 (by decide),orderAway 24 (by decide),
    headerAway 0 (by decide),headerAway 8 (by decide),headerAway 16 (by decide),headerAway 24 (by decide),orderHeader]

/-- Every real fresh-leaf cell has its actual last stored value. All
destinations are physically distinct under the real allocated geometry. -/
theorem stored_cell (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos value : BitVec 64)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (posInside : pos.toNat ≤ cap.toNat)
    (entry : BitVec 64 × BitVec 64) (member : entry ∈ storedWrites table cap node pos value) :
    (stored source table cap node pos value).memory entry.1 = .word entry.2 := by
  rw [stored_memory]
  exact WordWrites.write_unique _ _ entry (stored_writes_distinct table cap node pos value geometry inside posInside) member

theorem model_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (posInside : pos.toNat ≤ cap.toNat) :
    (model source table cap node pos pointer value).memory (FindLeaf.cell (New.nodesPointer table cap) node 0) = .word 0#64 ∧
    (model source table cap node pos pointer value).memory (FindLeaf.cell (New.nodesPointer table cap) node 8) = .word value ∧
    (model source table cap node pos pointer value).memory (FindLeaf.cell (New.nodesPointer table cap) node 16) = .word pos ∧
    (model source table cap node pos pointer value).memory (FindLeaf.cell (New.nodesPointer table cap) node 24) = .word 256#64 ∧
    (model source table cap node pos pointer value).memory (slot (New.orderPointer table cap) pos 8) = .word node := by
  have cell := stored_cell (KeyCopy.result (New.putField source table 64 (node+1#64)) pointer (slot (New.keysPointer table) node 32))
    table cap node pos value geometry inside posInside
  exact ⟨cell (FindLeaf.cell (New.nodesPointer table cap) node 0,0#64) (by simp [storedWrites]),
    cell (FindLeaf.cell (New.nodesPointer table cap) node 8,value) (by simp [storedWrites]),
    cell (FindLeaf.cell (New.nodesPointer table cap) node 16,pos) (by simp [storedWrites]),
    cell (FindLeaf.cell (New.nodesPointer table cap) node 24,256#64) (by simp [storedWrites]),
    cell (slot (New.orderPointer table cap) pos 8,node) (by simp [storedWrites])⟩

end InitECandidate.Solver.Input.CurrentTable.NewLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.stored_writes_distinct
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.model_cells
