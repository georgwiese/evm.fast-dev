import Mathlib.Data.List.Basic

/-! Last-record-wins semantics of the unchanged witness dictionary. -/
namespace InitECandidate.Solver.WitnessRadix

variable {Key Value : Type} [DecidableEq Key]

/-- The dictionary semantics used by witness construction: the final record
for a key overwrites every earlier record for that key. -/
def lastValue (key : Key) : List (Key × Value) → Option Value
  | [] => none
  | entry :: rest =>
      match lastValue key rest with
      | some value => some value
      | none => if entry.1 = key then some entry.2 else none

theorem lastValue_filter (key : Key) (input : List (Key × Value))
    (keep : Key → Bool) :
    lastValue key (input.filter fun entry => keep entry.1) =
      if keep key then lastValue key input else none := by
  induction input with
  | nil => simp [lastValue]
  | cons entry rest ih =>
      by_cases same : entry.1 = key
      · cases kept : keep key <;> cases tail : lastValue key rest <;>
          simp [List.filter_cons, lastValue, ih, same, kept, tail]
      · cases kept : keep entry.1 <;> cases queried : keep key <;>
          cases tail : lastValue key rest <;>
          simp [List.filter_cons, lastValue, ih, same, kept, queried, tail]

end InitECandidate.Solver.WitnessRadix

#print axioms InitECandidate.Solver.WitnessRadix.lastValue_filter
