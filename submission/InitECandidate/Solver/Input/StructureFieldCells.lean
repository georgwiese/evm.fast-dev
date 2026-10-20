import InitECandidate.Solver.Input.StructureFields

namespace InitECandidate.Solver.Input.StructureStore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes

/-- Distinct byte offsets in a real ordinary arena designate distinct words. -/
theorem field_address_eq (cursor : BitVec 64) (size left right : Nat) (arena : Arena cursor size) (leftSmall : left < size) (rightSmall : right < size) :
    (cursor + BitVec.ofNat 64 left = cursor + BitVec.ofNat 64 right) ↔ left = right := by
  have upper := arena.upper
  have number (offset : Nat) (small : offset < size) : (cursor + BitVec.ofNat 64 offset).toNat = cursor.toNat + offset :=
    byteAddress_toNat cursor offset (by omega)
  constructor
  · intro same
    have natural := congrArg BitVec.toNat same
    rw [number left leftSmall,number right rightSmall] at natural
    omega
  · intro same; rw [same]

/-- Read the exact final word of an actual structure-field sequence. The
arena size is the allocated size, including80-byte requests and96-byte SI. -/
theorem apply_fields_cell (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (size : Nat) (arena : Arena cursor size)
    (fields : List Field) (valid : ∀ field ∈ fields,field.1 < size) (offset : Nat) (small : offset < size) :
    (Payload.applyFields source cursor fields).memory (cursor + BitVec.ofNat 64 offset) =
      Payload.cellValue fields (source.memory (cursor + BitVec.ofNat 64 offset)) offset := by
  induction fields generalizing source with
  | nil => rfl
  | cons field rest ih =>
    rw [Payload.applyFields_cons,ih _ (by intro entry member; exact valid entry (by simp [member]))]
    simp only [Payload.cellValue,Payload.fieldStored,StoreWord.put,field_address_eq cursor size offset field.1 arena small (valid field (by simp))]

end InitECandidate.Solver.Input.StructureStore

#print axioms InitECandidate.Solver.Input.StructureStore.field_address_eq
#print axioms InitECandidate.Solver.Input.StructureStore.apply_fields_cell
