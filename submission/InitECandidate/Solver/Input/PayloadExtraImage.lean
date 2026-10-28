import InitECandidate.Solver.Input.PayloadPrefixImage
import InitECandidate.Solver.Input.PayloadExtraStores

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- The actual two extra-data stores produce the prefix image while retaining
the raw payload pointer established by the allocation/header prefix. -/
theorem extra_stored_image (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer record : BitVec 64) (room : record.toNat + 136 ≤ 33806089496)
    (raw : source.memory record = .word (pointer + 62#64))
    (extraBound : Guest.GasLimit.le32 input 566 - 540 ≤ 32) :
    PrefixImage input (extraStoredPayload source input pointer record) pointer record := by
  have base16 : record ≠ record + 16#64 := by
    simpa using (field_address_eq record room 0 16 (by decide) (by decide)).not.mpr (by decide)
  have base24 : record ≠ record + 24#64 := by
    simpa using (field_address_eq record room 0 24 (by decide) (by decide)).not.mpr (by decide)
  have fields : record + 16#64 ≠ record + 24#64 :=
    (field_address_eq record room 16 24 (by decide) (by decide)).not.mpr (by decide)
  refine ⟨?_, ?_, ?_, extraBound⟩
  all_goals simp [extraStoredPayload, extraPointerStored, fieldStored, WitnessRadix.StoreWord.put, base16, base24, fields, raw]

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.extra_stored_image
