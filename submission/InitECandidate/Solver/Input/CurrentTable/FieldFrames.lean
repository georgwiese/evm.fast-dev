import InitECandidate.Solver.Input.CurrentTable.CellGeometry
import InitECandidate.Solver.Input.CurrentTable.FirstDiff.ByteReads
import InitECandidate.Solver.Input.CurrentTable.NewStores

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- All real key backing cells are beyond the allocated table header. -/
theorem New.Geometry.key_backing_after_table {table cap : BitVec 64} (geometry : New.Geometry table cap)
    (node : BitVec 64) (inside : node.toNat ≤ cap.toNat) (byte : Fin 32) :
    table.toNat+88 ≤ (panByteAlignHOL (width:=64) (slot (New.keysPointer table) node 32+BitVec.ofNat 64 byte.val)).toNat := by
  have arena := geometry.key_slot node inside
  have aligned := slot_aligned _ node cap 32 geometry.keys inside geometry.keysAligned (by decide)
  rw [MemoryBytes.aligned_offset _ byte.val byte.isLt aligned (by have := arena.upper; omega)]
  have number := byteAddress_toNat (slot (New.keysPointer table) node 32) (8*(byte.val/8))
    (by have := arena.upper; have := byte.isLt; omega)
  change (slot (New.keysPointer table) node 32+BitVec.ofNat 64 (8*(byte.val/8))).toNat = _ at number
  rw [number,slot_number _ node cap 32 geometry.keys inside]
  have := geometry.tableBefore
  omega

theorem header_key (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap value node : BitVec 64) (field : Nat) (key : KeyBits.Key)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (small : field < 88)
    (view : FirstDiff.ByteView source (slot (New.keysPointer table) node 32) key) :
    FirstDiff.ByteView (New.putField source table field value) (slot (New.keysPointer table) node 32) key := by
  apply StoreWord.byteView_away source (table+BitVec.ofNat 64 field) value _ key _ view
  intro byte same
  have lower := geometry.key_backing_after_table node inside byte
  have number := byteAddress_toNat table field (by have := geometry.table.upper; omega)
  change (table+BitVec.ofNat 64 field).toNat = table.toNat+field at number
  have equal := congrArg BitVec.toNat same
  rw [number] at equal
  omega

theorem header_node (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap value node : BitVec 64) (field offset : Nat)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (fieldSmall : field < 88) (offsetSmall : offset < 32) :
    (New.putField source table field value).memory (FindLeaf.cell (New.nodesPointer table cap) node offset) =
      source.memory (FindLeaf.cell (New.nodesPointer table cap) node offset) := by
  have away := Ne.symm (geometry.header_away node inside offset field offsetSmall fieldSmall)
  simp only [New.putField,StoreWord.put,if_neg away]

theorem header_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table value : BitVec 64) (field target : Nat)
    (arena : AllocatedBytes.Arena table 88) (fieldSmall : field < 88) (targetSmall : target < 88) (different : target ≠ field) :
    (New.putField source table field value).memory (table+BitVec.ofNat 64 target) = source.memory (table+BitVec.ofNat 64 target) := by
  have away := byteAddress_ne table target field (by have := arena.upper; omega) (by have := arena.upper; omega) different
  change table+BitVec.ofNat 64 target ≠ table+BitVec.ofNat 64 field at away
  simp only [New.putField,StoreWord.put,if_neg away]

theorem header_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (table value : BitVec 64) (field : Nat)
    (frame : LocalEffects.erase target = LocalEffects.erase source) :
    LocalEffects.erase (New.putField target table field value) = LocalEffects.erase (New.putField source table field value) := by
  have kept := congrArg (fun state => LocalEffects.erase (New.putField state table field value)) frame
  exact kept

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.header_key
#print axioms InitECandidate.Solver.Input.CurrentTable.header_node
#print axioms InitECandidate.Solver.Input.CurrentTable.header_other
