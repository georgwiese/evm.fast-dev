import InitECandidate.Solver.MutableTable.LayoutRepresentation32

namespace InitECandidate.Solver.MutableTable.Layout32
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem header_cell (plan : AllocatedLayout.Plan) (offset : Nat) :
    BitVec.ofNat 64 plan.table+BitVec.ofNat 64 offset=cell plan .header offset := offset_cell plan .header offset

structure Header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (key : BitVec 64) (count : Nat) : Prop where
  find : Find.HeaderData source (BitVec.ofNat 64 plan.table) (parameters plan key)
  values : source.memory (BitVec.ofNat 64 plan.table+40#64)=.word (BitVec.ofNat 64 (base plan .values))
  order : source.memory (BitVec.ofNat 64 plan.table+56#64)=.word (BitVec.ofNat 64 (base plan .order))
  position : source.memory (BitVec.ofNat 64 plan.table+64#64)=.word (BitVec.ofNat 64 (base plan .position))
  count : source.memory (BitVec.ofNat 64 plan.table+24#64)=.word (BitVec.ofNat 64 count)

theorem initial_header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain) (key : BitVec 64) :
    Header (TableNew.enteredState source plan) plan key 0 := by
  refine ⟨TableEmpty.entered_header source plan ready domain key,?_,?_,?_,TableEmpty.entered_count source plan ready⟩
  · exact TableEmpty.entered_before source plan ready 40 (by decide) _ (by simp [TableNew.beforeWrites,base])
  · rw [TableNew.entered_memory]
    exact TableNew.result_after source.memory source.be plan ready
      (BitVec.ofNat 64 plan.table+56#64,BitVec.ofNat 64 (base plan .order)) (by simp [TableNew.afterWrites,base])
  · rw [TableNew.entered_memory]
    exact TableNew.result_after source.memory source.be plan ready
      (BitVec.ofNat 64 plan.table+64#64,BitVec.ofNat 64 (base plan .position)) (by simp [TableNew.afterWrites,base])

/-- Constructor geometry protects every fixed header field from every real
insertion store. The count field is deliberately excluded. -/
theorem result_header_cell (memory : WordWrites.Memory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (key : BitVec 64) (index count offset : Nat)
    (indexInside : index<plan.capacity) (countInside : count<plan.capacity)
    (offsetInside : offset<72) (different : offset≠24) (value : BitVec 64) (words : Fin 4→BitVec 64) :
    resultMemory memory plan key index count value words (BitVec.ofNat 64 plan.table+BitVec.ofNat 64 offset)=
      memory (BitVec.ofNat 64 plan.table+BitVec.ofNat 64 offset) := by
  apply Insert.result_away
  · rw [header_cell plan offset]
    exact copy_away plan ready key index indexInside words .header offset offsetInside (by decide)
  · rw [header_cell plan offset,value_cell]
    exact separate plan ready .header .values (by decide) _ _ offsetInside (by change _<8*plan.capacity;omega)
  · rw [header_cell plan offset,used_byte_cell plan ready key index indexInside]
    exact separate plan ready .header .used (by decide) _ _ offsetInside (by change _<plan.capacity;omega)
  · rw [header_cell plan offset]
    exact metadata_away plan ready index count indexInside countInside .header offset offsetInside
      (by decide) (by decide) (Or.inr different)

/-- Actual final memory preserves all eight fixed fields and increments the
natural count without wrapping, from the constructor's checked layout. -/
theorem result_header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (key : BitVec 64) (index count : Nat)
    (indexInside : index<plan.capacity) (countInside : count<plan.capacity)
    (value : BitVec 64) (words : Fin 4→BitVec 64) (header : Header source plan key count) :
    Header {source with memory:=resultMemory source.memory plan key index count value words} plan key (count+1) := by
  have fixed (offset : Nat) (inside : offset<72) (different : offset≠24):=
    result_header_cell source.memory plan ready key index count offset indexInside countInside inside different value words
  refine ⟨⟨header.find.mapped,?_,?_,?_,?_,?_⟩,?_,?_,?_,?_⟩
  · exact (fixed 16 (by decide) (by decide)).trans header.find.capacity
  · simpa only [BitVec.add_zero] using (fixed 0 (by decide) (by decide)).trans
      (show source.memory (BitVec.ofNat 64 plan.table+0#64)=.word (parameters plan key).keyLength by simpa using header.find.keyLength)
  · exact (fixed 8 (by decide) (by decide)).trans header.find.stride
  · exact (fixed 32 (by decide) (by decide)).trans header.find.keys
  · exact (fixed 48 (by decide) (by decide)).trans header.find.used
  · exact (fixed 40 (by decide) (by decide)).trans header.values
  · exact (fixed 56 (by decide) (by decide)).trans header.order
  · exact (fixed 64 (by decide) (by decide)).trans header.position
  · rw [show BitVec.ofNat 64 (count+1)=BitVec.ofNat 64 count+1#64 from BitVec.ofNat_add count 1]
    exact Insert.result_count source.memory _ _ _ _ _ _ _ _ words

end InitECandidate.Solver.MutableTable.Layout32

#print axioms InitECandidate.Solver.MutableTable.Layout32.initial_header
#print axioms InitECandidate.Solver.MutableTable.Layout32.result_header_cell
#print axioms InitECandidate.Solver.MutableTable.Layout32.result_header
