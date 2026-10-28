import InitECandidate.Solver.Input.CurrentTable.NewLeaf.Key

namespace InitECandidate.Solver.Input.CurrentTable.NewLeaf
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem order_after_table (table cap pos : BitVec 64) (geometry : New.Geometry table cap) (inside : pos.toNat ≤ cap.toNat) :
    table.toNat+88 ≤ (slot (New.orderPointer table cap) pos 8).toNat := by
  rw [slot_number _ pos cap 8 geometry.order inside]
  have := geometry.tableBefore
  have := geometry.keysBefore
  have := geometry.nodesBefore
  omega

theorem order_header_away (table cap pos : BitVec 64) (geometry : New.Geometry table cap) (inside : pos.toNat ≤ cap.toNat)
    (field : Nat) (small : field < 88) : table+BitVec.ofNat 64 field ≠ slot (New.orderPointer table cap) pos 8 := by
  have afterTable := order_after_table table cap pos geometry inside
  have number := byteAddress_toNat table field (by have := geometry.table.upper; omega)
  change (table+BitVec.ofNat 64 field).toNat = table.toNat+field at number
  intro same
  have equal := congrArg BitVec.toNat same
  rw [number] at equal
  omega

/-- All leaf writes except its final count store preserve the header. -/
theorem stored_header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos value : BitVec 64)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (posInside : pos.toNat ≤ cap.toNat)
    (field : Nat) (small : field < 88) (different : field ≠ 24) :
    (stored source table cap node pos value).memory (table+BitVec.ofNat 64 field) = source.memory (table+BitVec.ofNat 64 field) := by
  have nodeAway (offset : Nat) (offsetInside : offset < 32) := geometry.header_away node inside offset field offsetInside small
  have orderAway := order_header_away table cap pos geometry posInside field small
  have countAway := byteAddress_ne table field 24 (by have := geometry.table.upper; omega) (by have := geometry.table.upper; omega) different
  change table+BitVec.ofNat 64 field ≠ table+24#64 at countAway
  rw [stored_memory]
  apply WordWrites.write_away
  simpa only [storedWrites,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,not_or] using
    And.intro (nodeAway 0 (by decide)) (And.intro (nodeAway 8 (by decide)) (And.intro (nodeAway 16 (by decide))
      (And.intro (nodeAway 24 (by decide)) (And.intro orderAway countAway))))

theorem model_header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (posInside : pos.toNat ≤ cap.toNat)
    (field : Nat) (small : field < 88) (notCount : field ≠ 24) (notNext : field ≠ 64) :
    (model source table cap node pos pointer value).memory (table+BitVec.ofNat 64 field) = source.memory (table+BitVec.ofNat 64 field) := by
  rw [model,stored_header _ table cap node pos value geometry inside posInside field small notCount]
  rw [KeyCopy.memory_before _ pointer _ _ (geometry.key_slot node inside)]
  · have away := byteAddress_ne table field 64 (by have := geometry.table.upper; omega) (by have := geometry.table.upper; omega) notNext
    change table+BitVec.ofNat 64 field ≠ table+64#64 at away
    simp only [New.putField,StoreWord.put,if_neg away]
  · have number := byteAddress_toNat table field (by have := geometry.table.upper; omega)
    change (table+BitVec.ofNat 64 field).toNat = table.toNat+field at number
    rw [number,slot_number _ node cap 32 geometry.keys inside]
    have := geometry.tableBefore
    omega

theorem model_count (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) :
    (model source table cap node pos pointer value).memory (table+24#64) = .word (pos+1#64) := by
  simp [model,stored,tailStored,New.putField,StoreWord.put]

theorem model_next (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (posInside : pos.toNat ≤ cap.toNat) :
    (model source table cap node pos pointer value).memory (table+64#64) = .word (node+1#64) := by
  rw [model,stored_header _ table cap node pos value geometry inside posInside 64 (by decide) (by decide)]
  rw [KeyCopy.memory_before _ pointer _ _ (geometry.key_slot node inside)]
  · simp [New.putField,StoreWord.put]
  · have number := byteAddress_toNat table 64 (by have := geometry.table.upper; omega)
    change (table+64#64).toNat = table.toNat+64 at number
    rw [number,slot_number _ node cap 32 geometry.keys inside]
    have := geometry.tableBefore
    omega

end InitECandidate.Solver.Input.CurrentTable.NewLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.model_header
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.model_count
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.model_next
