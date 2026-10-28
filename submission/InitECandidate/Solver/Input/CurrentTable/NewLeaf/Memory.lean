import InitECandidate.Solver.Input.CurrentTable.NewLeaf.Call

namespace InitECandidate.Solver.Input.CurrentTable.NewLeaf
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Exact write footprint of the original leaf constructor. The four copy
words are those actually read after the allocator's metadata increment. -/
def writes (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) : List (BitVec 64 × BitVec 64) :=
  let words := MemoryBytes.wordsOf (New.putField source table 64 (node+1#64)) pointer
  let dst := slot (New.keysPointer table) node 32
  let base := New.nodesPointer table cap
  [(table+64#64,node+1#64),(dst,words 0),(dst+8#64,words 1),(dst+16#64,words 2),(dst+24#64,words 3),
    (FindLeaf.cell base node 0,0#64),(FindLeaf.cell base node 8,value),(FindLeaf.cell base node 16,pos),
    (FindLeaf.cell base node 24,256#64),(slot (New.orderPointer table cap) pos 8,node),(table+24#64,pos+1#64)]

theorem model_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) :
    (model source table cap node pos pointer value).memory = WordWrites.write source.memory (writes source table cap node pos pointer value) := rfl

theorem memory_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value query : BitVec 64)
    (away : query ∉ (writes source table cap node pos pointer value).map Prod.fst) :
    (model source table cap node pos pointer value).memory query = source.memory query := by
  rw [model_memory]
  exact WordWrites.write_away _ _ _ away

theorem write_after_table (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (posInside : pos.toNat ≤ cap.toNat)
    (entry : BitVec 64 × BitVec 64) (member : entry ∈ writes source table cap node pos pointer value) : table.toNat ≤ entry.1.toNat := by
  have header (offset : Nat) (small : offset < 88) : table.toNat ≤ (table+BitVec.ofNat 64 offset).toNat := by
    have number := byteAddress_toNat table offset (by have := geometry.table.upper; omega)
    change (table+BitVec.ofNat 64 offset).toNat = table.toNat+offset at number
    omega
  have copy (offset : Nat) (small : offset < 32) : table.toNat ≤ (slot (New.keysPointer table) node 32+BitVec.ofNat 64 offset).toNat := by
    have arena := geometry.key_slot node inside
    have number := byteAddress_toNat (slot (New.keysPointer table) node 32) offset (by have := arena.upper; omega)
    change (slot (New.keysPointer table) node 32+BitVec.ofNat 64 offset).toNat = _ at number
    rw [number,slot_number _ node cap 32 geometry.keys inside]
    have := geometry.tableBefore
    omega
  have cell (offset : Nat) (small : offset < 32) : table.toNat ≤ (FindLeaf.cell (New.nodesPointer table cap) node offset).toNat := by
    have := geometry.cell_after_table node inside offset small
    omega
  have order : table.toNat ≤ (slot (New.orderPointer table cap) pos 8).toNat := by
    rw [slot_number _ pos cap 8 geometry.order posInside]
    have := geometry.tableBefore
    have := geometry.keysBefore
    have := geometry.nodesBefore
    omega
  simp only [writes,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact header 64 (by decide)
  · simpa only [BitVec.add_zero] using copy 0 (by decide)
  · exact copy 8 (by decide)
  · exact copy 16 (by decide)
  · exact copy 24 (by decide)
  · exact cell 0 (by decide)
  · exact cell 8 (by decide)
  · exact cell 16 (by decide)
  · exact cell 24 (by decide)
  · exact order
  · exact header 24 (by decide)

/-- Real leaf allocation/copy/stores preserve every earlier input word. -/
theorem memory_before (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value query : BitVec 64)
    (geometry : New.Geometry table cap) (inside : node.toNat ≤ cap.toNat) (posInside : pos.toNat ≤ cap.toNat)
    (before : query.toNat < table.toNat) :
    (model source table cap node pos pointer value).memory query = source.memory query := by
  apply memory_away
  intro member
  obtain ⟨entry,member,same⟩ := List.mem_map.mp member
  have afterTable := write_after_table source table cap node pos pointer value geometry inside posInside entry member
  rw [same] at afterTable
  omega

end InitECandidate.Solver.Input.CurrentTable.NewLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.model_memory
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.memory_away
#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.memory_before
