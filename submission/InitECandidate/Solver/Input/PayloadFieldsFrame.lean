import InitECandidate.Solver.Input.PayloadFields
import InitECandidate.Solver.Input.VarList.RecordsAfterFrame

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Literal scalar field writes leave every other physical cell unchanged. -/
theorem applyFields_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor query : BitVec 64)
    (fields : List Field) (away : ∀ field ∈ fields, query ≠ cursor + BitVec.ofNat 64 field.1) :
    (applyFields source cursor fields).memory query = source.memory query := by
  induction fields generalizing source with
  | nil => rfl
  | cons field rest ih =>
    rw [applyFields_cons, ih _ (by intro item member; exact away item (by simp [member]))]
    simp [fieldStored, WitnessRadix.StoreWord.put, away field (by simp)]

/-- All later payload writes stay within its136-byte record and preserve the
complete already initialized transaction array, including empty-array cases. -/
theorem applyFields_records (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor array : BitVec 64) (start length : Nat) (fields : List Field)
    (records : VarList.Records source input pointer array start length)
    (after : cursor.toNat + 136 ≤ array.toNat) (room : cursor.toNat + 136 ≤ 33806089496)
    (valid : ∀ field ∈ fields, field.1 ≤ 128) :
    VarList.Records (applyFields source cursor fields) input pointer array start length := by
  apply VarList.Records.of_after source _ input pointer array start length array.toNat records (Nat.le_refl _)
  intro query lower
  apply applyFields_away
  intro field member same
  have small := valid field member
  have number : (cursor + BitVec.ofNat 64 field.1).toNat = cursor.toNat + field.1 := by
    have encoded : (BitVec.ofNat 64 field.1).toNat = field.1 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add_of_lt (by rw [encoded]; omega), encoded]
  rw [same, number] at lower
  omega

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.applyFields_away
#print axioms InitECandidate.Solver.Input.Payload.applyFields_records
