import InitECandidate.Solver.Input.PayloadPrefixImage

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Every actual later payload field is beyond the early hashing prefix. -/
theorem PrefixImage.fields_after {input : Guest.InputBlob}
    {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer record : BitVec 64}
    (data : PrefixImage input source pointer record) (fields : List Field)
    (room : record.toNat + 136 ≤ 33806089496) (valid : ∀ field ∈ fields, 32 ≤ field.1 ∧ field.1 ≤ 128) :
    PrefixImage input (applyFields source record fields) pointer record := by
  induction fields generalizing source with
  | nil => exact data
  | cons field rest ih =>
    have bound := valid field (by simp)
    rw [applyFields_cons]
    exact ih (data.store_after field.1 field.2.2 bound.1 bound.2 room)
      (by intro item member; exact valid item (by simp [member]))

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.PrefixImage.fields_after
