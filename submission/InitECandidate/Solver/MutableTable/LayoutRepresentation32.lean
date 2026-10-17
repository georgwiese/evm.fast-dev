import InitECandidate.Solver.MutableTable.LayoutData32

namespace InitECandidate.Solver.MutableTable.Layout32
open Flapjack PanSemStateFiniteExact WitnessRadix

def resultMemory (memory : WordWrites.Memory) (plan : AllocatedLayout.Plan) (keyPointer : BitVec 64)
    (index count : Nat) (value : BitVec 64) (words : Fin 4→BitVec 64) : WordWrites.Memory:=
  Insert.resultMemory memory (parameters plan keyPointer) (BitVec.ofNat 64 plan.table)
    (BitVec.ofNat 64 (base plan .values)) (BitVec.ofNat 64 (base plan .order)) (BitVec.ofNat 64 (base plan .position))
    (BitVec.ofNat 64 index) (BitVec.ofNat 64 count) value words

/-- The real constructor layout discharges every physical ownership premise
for value representation after the full insertion-memory transformation. -/
theorem result_values (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (keyPointer : BitVec 64) (index count : Nat) (indexInside : index<plan.capacity) (countInside : count<plan.capacity)
    (logical : Find.Model32 (BitVec 64)) (key : Find.Key32) (value : BitVec 64) (words : Fin 4→BitVec 64)
    (model : Find.ValueModel32 source (BitVec.ofNat 64 (base plan .values)) plan.capacity logical) :
    Find.ValueModel32 {source with memory:=resultMemory source.memory plan keyPointer index count value words}
      (BitVec.ofNat 64 (base plan .values)) plan.capacity (Placement.put logical index key value) := by
  apply Insert.result_values source (parameters plan keyPointer) plan.capacity index indexInside logical
    (BitVec.ofNat 64 plan.table) _ _ _ (BitVec.ofNat 64 count) value key words model (values_fit plan ready)
  · rw [value_cell]
    exact word_mapped source plan ready domain .values _ (by change _<8*plan.capacity;omega) (by omega)
  · intro i inside
    rw [value_cell]
    exact copy_away plan ready keyPointer index indexInside words .values _ (by change _<8*plan.capacity;omega) (by decide)
  · intro i inside
    rw [value_cell,used_byte_cell plan ready keyPointer index indexInside]
    exact separate plan ready .values .used (by decide) _ _ (by change _<8*plan.capacity;omega) (by change _<plan.capacity;omega)
  · intro i inside
    rw [value_cell]
    exact metadata_away plan ready index count indexInside countInside .values _ (by change _<8*plan.capacity;omega)
      (by decide) (by decide) (Or.inl (by decide))

/-- Concrete constructor allocation geometry supplies all copy, byte-store
and metadata separation for the full original key/used-byte representation. -/
theorem result_keys (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (keyPointer : BitVec 64) (index count : Nat) (indexInside : index<plan.capacity) (countInside : count<plan.capacity)
    (logical : Find.Model32 (BitVec 64)) (key : Find.Key32) (value : BitVec 64) (words : Fin 4→BitVec 64)
    (model : Find.KeyModel32 source (parameters plan keyPointer) plan.capacity logical)
    (sourceAligned : keyPointer.toNat%8=0) (sourceFits : keyPointer.toNat+32<2^64) (little : source.be=false)
    (sourceWords : MemoryBytes.WordView source keyPointer words) (sourceBytes : MemoryBytes.ByteView source keyPointer key) :
    Find.KeyModel32 {source with memory:=resultMemory source.memory plan keyPointer index count value words}
      (parameters plan keyPointer) plan.capacity (Placement.put logical index key value) := by
  have fits:=ready.fits
  apply Insert.result_keys source (parameters plan keyPointer) plan.capacity index indexInside (by omega) logical model
    (BitVec.ofNat 64 plan.table) (BitVec.ofNat 64 (base plan .values)) (BitVec.ofNat 64 (base plan .order))
    (BitVec.ofNat 64 (base plan .position)) (BitVec.ofNat 64 count) value key words sourceAligned sourceFits
    (key_aligned plan ready keyPointer index indexInside) (key_fits plan ready keyPointer index indexInside) little
    sourceWords sourceBytes (key_mapped source plan ready domain keyPointer index indexInside)
    (used_mapped source plan ready domain keyPointer index indexInside)
  · intro i inside
    rw [used_byte_cell plan ready keyPointer i inside]
    exact copy_away plan ready keyPointer index indexInside words .used _ (by change _<plan.capacity;omega) (by decide)
  · intro i inside different byte
    exact old_keys_copy_away plan ready keyPointer index i byte.val indexInside inside different byte.isLt words
  · intro i inside
    rw [used_byte_cell plan ready keyPointer i inside,value_cell]
    exact separate plan ready .used .values (by decide) _ _ (by change _<plan.capacity;omega) (by change _<8*plan.capacity;omega)
  · intro i inside byte
    rw [key_byte_cell plan ready keyPointer i byte.val inside byte.isLt,value_cell]
    exact separate plan ready .keys .values (by decide) _ _ (by change _<32*plan.capacity;have:=byte.isLt;omega)
      (by change _<8*plan.capacity;omega)
  · intro i inside byte
    rw [key_cell,used_cell]
    exact separate plan ready .keys .used (by decide) _ _ (by change _<32*plan.capacity;have:=byte.isLt;omega) indexInside
  · intro i inside
    rw [used_byte_cell plan ready keyPointer i inside]
    exact metadata_away plan ready index count indexInside countInside .used _ (by change _<plan.capacity;omega)
      (by decide) (by decide) (Or.inl (by decide))
  · intro i inside byte
    rw [key_byte_cell plan ready keyPointer i byte.val inside byte.isLt]
    exact metadata_away plan ready index count indexInside countInside .keys _ (by change _<32*plan.capacity;have:=byte.isLt;omega)
      (by decide) (by decide) (Or.inl (by decide))

end InitECandidate.Solver.MutableTable.Layout32

#print axioms InitECandidate.Solver.MutableTable.Layout32.result_values
#print axioms InitECandidate.Solver.MutableTable.Layout32.result_keys
