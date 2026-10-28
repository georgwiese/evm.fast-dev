import InitECandidate.Solver.Input.CurrentTable.NewLeaf.Memory
import InitECandidate.Solver.Input.WordWritesBytes

namespace InitECandidate.Solver.Input.CurrentTable.NewLeaf
open Flapjack PanSemStateFiniteExact WitnessRadix

def storedWrites (table cap node pos value : BitVec 64) : List (BitVec 64 × BitVec 64) :=
  [(FindLeaf.cell (New.nodesPointer table cap) node 0,0#64),
    (FindLeaf.cell (New.nodesPointer table cap) node 8,value),
    (FindLeaf.cell (New.nodesPointer table cap) node 16,pos),
    (FindLeaf.cell (New.nodesPointer table cap) node 24,256#64),
    (slot (New.orderPointer table cap) pos 8,node),(table+24#64,pos+1#64)]

theorem stored_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos value : BitVec 64) :
    (stored source table cap node pos value).memory = WordWrites.write source.memory (storedWrites table cap node pos value) := rfl

set_option maxHeartbeats 1000000 in
/-- All actual node/order/count writes protect every key-array byte,
including its physical aligned backing word. -/
theorem stored_key (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos value keyNode : BitVec 64) (key : KeyBits.Key)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (posInside : pos.toNat ≤ cap.toNat)
    (keyInside : keyNode.toNat ≤ cap.toNat)
    (view : FirstDiff.ByteView source (slot (New.keysPointer table) keyNode 32) key) :
    FirstDiff.ByteView (stored source table cap node pos value) (slot (New.keysPointer table) keyNode 32) key := by
  have away (entry : BitVec 64 × BitVec 64) (member : entry ∈ storedWrites table cap node pos value) (byte : Fin 32) :
      panByteAlignHOL (width:=64) (slot (New.keysPointer table) keyNode 32+BitVec.ofNat 64 byte.val) ≠ entry.1 := by
    let backing := panByteAlignHOL (width:=64) (slot (New.keysPointer table) keyNode 32+BitVec.ofNat 64 byte.val)
    have nodeAway (offset : Nat) (small : offset < 32) : backing ≠ FindLeaf.cell (New.nodesPointer table cap) node offset := by
      have before := geometry.key_byte_before_node keyNode node keyInside inside byte.val offset byte.isLt small
      intro same
      have equal := congrArg BitVec.toNat same
      change backing.toNat < _ at before
      omega
    have keyArena := geometry.key_slot keyNode keyInside
    have keyNumber := slot_number (New.keysPointer table) keyNode cap 32 geometry.keys keyInside
    have byteNumber := byteAddress_toNat (slot (New.keysPointer table) keyNode 32) byte.val (by have := keyArena.upper; have := byte.isLt; omega)
    have backingNumber := AllocatedBytes.aligned_number (byteAddress (slot (New.keysPointer table) keyNode 32) byte.val)
    change backing.toNat = _ at backingNumber
    rw [byteNumber,keyNumber] at backingNumber
    have keyAligned := slot_aligned (New.keysPointer table) keyNode cap 32 geometry.keys keyInside geometry.keysAligned (by decide)
    rw [keyNumber] at keyAligned
    have lower : (New.keysPointer table).toNat ≤ backing.toNat := by omega
    have upper : backing.toNat < (New.orderPointer table cap).toNat := by
      have := geometry.keysBefore
      have := geometry.nodesBefore
      have := byte.isLt
      omega
    have orderAway : backing ≠ slot (New.orderPointer table cap) pos 8 := by
      have number := slot_number (New.orderPointer table cap) pos cap 8 geometry.order posInside
      intro same
      have equal := congrArg BitVec.toNat same
      rw [number] at equal
      omega
    have headerAway : backing ≠ table+24#64 := by
      have number := byteAddress_toNat table 24 (by have := geometry.table.upper; omega)
      change (table+24#64).toNat = table.toNat+24 at number
      have := geometry.tableBefore
      intro same
      have equal := congrArg BitVec.toNat same
      rw [number] at equal
      omega
    simp only [storedWrites,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact nodeAway 0 (by decide)
    · exact nodeAway 8 (by decide)
    · exact nodeAway 16 (by decide)
    · exact nodeAway 24 (by decide)
    · exact orderAway
    · exact headerAway
  have kept := word_writes_bytes source (storedWrites table cap node pos value) (slot (New.keysPointer table) keyNode 32) key away view
  exact kept

/-- The returned fresh leaf's physical bytes are the reached query bytes,
after the actual metadata increment, copy and every original leaf store. -/
theorem model_key (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) (key : KeyBits.Key)
    (fields : Fields source table cap node pos pointer key) (beforeTable : pointer.toNat+32 ≤ table.toNat) :
    FirstDiff.ByteView (model source table cap node pos pointer value) (slot (New.keysPointer table) node 32) key := by
  have allocated := fields.after_next beforeTable
  exact stored_key _ table cap node pos value node key fields.geometry fields.inside fields.posInside fields.inside allocated.copy.copied

end InitECandidate.Solver.Input.CurrentTable.NewLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.stored_key
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.model_key
