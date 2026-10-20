import InitECandidate.Solver.Input.PayloadFields

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

/-- Field-memory updates compose in their actual source order. -/
theorem fieldMemory_append (memory : BitVec 64→HolWordLab 64) (cursor : BitVec 64) (left right : List Field) :
    fieldMemory memory cursor (left++right)=fieldMemory (fieldMemory memory cursor left) cursor right := by
  induction left generalizing memory with
  | nil => rfl
  | cons field rest ih => exact ih (StoreWord.put memory (cursor+BitVec.ofNat 64 field.1) field.2.2)

/-- Matching the old value at one physical word suffices for any shared list
of constant field writes to match at that same word. -/
theorem fieldMemory_point (left right : BitVec 64→HolWordLab 64) (cursor query : BitVec 64) (fields : List Field)
    (same : left query=right query) : fieldMemory left cursor fields query=fieldMemory right cursor fields query := by
  induction fields generalizing left right with
  | nil => exact same
  | cons field rest ih =>
    apply ih
    simp only [StoreWord.put]
    split
    · rfl
    · exact same

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.fieldMemory_append
#print axioms InitECandidate.Solver.Input.Payload.fieldMemory_point
