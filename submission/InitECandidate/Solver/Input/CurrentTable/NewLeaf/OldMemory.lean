import InitECandidate.Solver.Input.CurrentTable.NewLeaf.Cells

namespace InitECandidate.Solver.Input.CurrentTable.NewLeaf
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Fresh leaf allocation cannot change any cell of an earlier node. -/
theorem model_old_node (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value oldNode : BitVec 64)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (posInside : pos.toNat ≤ cap.toNat)
    (oldInside : oldNode.toNat ≤ cap.toNat) (different : oldNode ≠ node) (offset : Nat) (small : offset < 32) :
    (model source table cap node pos pointer value).memory (FindLeaf.cell (New.nodesPointer table cap) oldNode offset) =
      source.memory (FindLeaf.cell (New.nodesPointer table cap) oldNode offset) := by
  let address := FindLeaf.cell (New.nodesPointer table cap) oldNode offset
  have headerAway (field : Nat) (fieldInside : field < 88) : address ≠ table+BitVec.ofNat 64 field :=
    Ne.symm (geometry.header_away oldNode oldInside offset field small fieldInside)
  have nodeAway (field : Nat) (fieldInside : field < 32) : address ≠ FindLeaf.cell (New.nodesPointer table cap) node field := by
    intro same
    exact different (cell_injective _ oldNode node cap offset field geometry.nodes oldInside inside small fieldInside same).1
  have orderAway : address ≠ slot (New.orderPointer table cap) pos 8 := by
    have before := node_before_order table cap oldNode pos geometry oldInside posInside offset small
    intro same
    have equal := congrArg BitVec.toNat same
    change address.toNat < _ at before
    omega
  have copyAway (byte : Nat) (byteInside : byte < 32) : address ≠ slot (New.keysPointer table) node 32+BitVec.ofNat 64 byte := by
    have keyArena := geometry.key_slot node inside
    have number := byteAddress_toNat (slot (New.keysPointer table) node 32) byte (by have := keyArena.upper; omega)
    change (slot (New.keysPointer table) node 32+BitVec.ofNat 64 byte).toNat = _ at number
    rw [slot_number _ node cap 32 geometry.keys inside] at number
    have addrNumber := cell_number _ oldNode cap offset geometry.nodes oldInside small
    have := geometry.keysBefore
    intro same
    have equal := congrArg BitVec.toNat same
    change address.toNat = _ at equal
    rw [number] at equal
    change address.toNat = _ at addrNumber
    omega
  apply memory_away
  simp only [writes,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,not_or]
  exact ⟨headerAway 64 (by decide),by simpa only [BitVec.add_zero] using copyAway 0 (by decide),
    copyAway 8 (by decide),copyAway 16 (by decide),copyAway 24 (by decide),
    nodeAway 0 (by decide),nodeAway 8 (by decide),nodeAway 16 (by decide),nodeAway 24 (by decide),orderAway,headerAway 24 (by decide)⟩

/-- The real fresh key copy preserves every different existing key slot.
Its backing cells cannot alias any of the four copied word destinations. -/
theorem copy_old_key (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pointer oldNode : BitVec 64) (key : KeyBits.Key)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (oldInside : oldNode.toNat ≤ cap.toNat)
    (different : oldNode ≠ node) (view : FirstDiff.ByteView source (slot (New.keysPointer table) oldNode 32) key) :
    FirstDiff.ByteView (KeyCopy.result source pointer (slot (New.keysPointer table) node 32)) (slot (New.keysPointer table) oldNode 32) key := by
  apply word_writes_bytes source (Copy32.writes (slot (New.keysPointer table) node 32) (MemoryBytes.wordsOf source pointer)) _ key _ view
  intro entry member byte
  have oldArena := geometry.key_slot oldNode oldInside
  have aligned := slot_aligned _ oldNode cap 32 geometry.keys oldInside geometry.keysAligned (by decide)
  have backing := MemoryBytes.aligned_offset (slot (New.keysPointer table) oldNode 32) byte.val byte.isLt aligned (by have := oldArena.upper; omega)
  have apart (offset : Nat) (small : offset < 32) :
      panByteAlignHOL (width:=64) (slot (New.keysPointer table) oldNode 32+BitVec.ofNat 64 byte.val) ≠
        slot (New.keysPointer table) node 32+BitVec.ofNat 64 offset := by
    rw [backing]
    intro same
    have equal := cell_injective (New.keysPointer table) oldNode node cap (8*(byte.val/8)) offset geometry.keys oldInside inside
      (by have := byte.isLt; omega) small same
    exact different equal.1
  simp only [Copy32.writes,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · simpa only [BitVec.add_zero] using apart 0 (by decide)
  · exact apart 8 (by decide)
  · exact apart 16 (by decide)
  · exact apart 24 (by decide)

/-- The original allocator metadata update, new key copy and leaf writes
retain every previously stored key in a different allocated slot. -/
theorem model_old_key (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value oldNode : BitVec 64) (key : KeyBits.Key)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (posInside : pos.toNat ≤ cap.toNat)
    (oldInside : oldNode.toNat ≤ cap.toNat) (different : oldNode ≠ node)
    (view : FirstDiff.ByteView source (slot (New.keysPointer table) oldNode 32) key) :
    FirstDiff.ByteView (model source table cap node pos pointer value) (slot (New.keysPointer table) oldNode 32) key := by
  have allocated : FirstDiff.ByteView (New.putField source table 64 (node+1#64)) (slot (New.keysPointer table) oldNode 32) key := by
    apply StoreWord.byteView_away source (table+64#64) (node+1#64) _ key _ view
    intro byte same
    have arena := geometry.key_slot oldNode oldInside
    have aligned := slot_aligned _ oldNode cap 32 geometry.keys oldInside geometry.keysAligned (by decide)
    have backing := MemoryBytes.aligned_offset (slot (New.keysPointer table) oldNode 32) byte.val byte.isLt aligned (by have := arena.upper; omega)
    have number := byteAddress_toNat (slot (New.keysPointer table) oldNode 32) (8*(byte.val/8))
      (by have := arena.upper; have := byte.isLt; omega)
    change (slot (New.keysPointer table) oldNode 32+BitVec.ofNat 64 (8*(byte.val/8))).toNat = _ at number
    rw [slot_number _ oldNode cap 32 geometry.keys oldInside] at number
    have headerNumber := byteAddress_toNat table 64 (by have := geometry.table.upper; omega)
    change (table+64#64).toNat = table.toNat+64 at headerNumber
    rw [backing] at same
    have equal := congrArg BitVec.toNat same
    rw [number,headerNumber] at equal
    have := geometry.tableBefore
    omega
  have copied := copy_old_key (New.putField source table 64 (node+1#64)) table cap node pointer oldNode key geometry inside oldInside different allocated
  exact stored_key _ table cap node pos value oldNode key geometry inside posInside oldInside copied

end InitECandidate.Solver.Input.CurrentTable.NewLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.model_old_node
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.copy_old_key
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.model_old_key
