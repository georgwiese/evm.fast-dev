import InitECandidate.Solver.Input.StructureFieldCells

namespace InitECandidate.Solver.Input.StructureStore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes

theorem field_memory_away (memory : BitVec 64 → HolWordLab 64) (cursor query : BitVec 64) (fields : List Field)
    (away : ∀ field ∈ fields,query ≠ cursor + BitVec.ofNat 64 field.1) : Payload.fieldMemory memory cursor fields query = memory query := by
  induction fields generalizing memory with
  | nil => rfl
  | cons field rest ih =>
    rw [Payload.fieldMemory,ih _ (by intro next member; exact away next (by simp [member]))]
    simp only [StoreWord.put,if_neg (away field (by simp))]

/-- Every word outside the actual allocated structure survives its writes. -/
theorem apply_fields_outside (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (size : Nat) (arena : Arena cursor size)
    (fields : List Field) (valid : ∀ field ∈ fields,field.1 < size) (query : BitVec 64)
    (outside : query.toNat < cursor.toNat ∨ cursor.toNat + size ≤ query.toNat) :
    (Payload.applyFields source cursor fields).memory query = source.memory query := by
  apply field_memory_away
  intro field member same
  have upper := arena.upper
  have small := valid field member
  have number : (cursor + BitVec.ofNat 64 field.1).toNat = cursor.toNat + field.1 := byteAddress_toNat cursor field.1 (by omega)
  have equal := congrArg BitVec.toNat same
  rw [number] at equal
  rcases outside with before | after <;> omega

end InitECandidate.Solver.Input.StructureStore

#print axioms InitECandidate.Solver.Input.StructureStore.field_memory_away
#print axioms InitECandidate.Solver.Input.StructureStore.apply_fields_outside
