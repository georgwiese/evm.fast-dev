import Mathlib.Data.List.Basic

/-! A compressed binary radix index for immutable witness records. The model
keeps stable record lists at leaves so that duplicate hashes retain the last
input value. The memory and machine realization are separate obligations. -/
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

inductive Index (Key Value : Type) where
  | empty
  | bucket (entries : List (Key × Value))
  | branch (position : Nat) (zero one : Index Key Value)
  deriving Repr

/-- Empty children are removed, so a long common key prefix occupies no nodes. -/
def join (position : Nat) : Index Key Value → Index Key Value → Index Key Value
  | .empty, other => other
  | other, .empty => other
  | zero, one => .branch position zero one

def lookup (bit : Key → Nat → Bool) (key : Key) : Index Key Value → Option Value
  | .empty => none
  | .bucket entries => lastValue key entries
  | .branch position zero one =>
      if bit key position then lookup bit key one else lookup bit key zero

theorem lookup_join (bit : Key → Nat → Bool) (key : Key) (position : Nat)
    (zero one : Index Key Value)
    (zeroSupport : bit key position = true → lookup bit key zero = none)
    (oneSupport : bit key position = false → lookup bit key one = none) :
    lookup bit key (join position zero one) =
      if bit key position then lookup bit key one else lookup bit key zero := by
  cases zero <;> cases one <;> cases h : bit key position <;>
    simp_all [join, lookup]

/-- Stable partition at successive key bits; unary levels are compressed. -/
def build (bit : Key → Nat → Bool) (position : Nat) :
    Nat → List (Key × Value) → Index Key Value
  | _, [] => .empty
  | 0, input => .bucket input
  | fuel + 1, input =>
      join position
        (build bit (position + 1) fuel (input.filter fun entry => !bit entry.1 position))
        (build bit (position + 1) fuel (input.filter fun entry => bit entry.1 position))

/-- Bulk construction preserves last-record-wins lookup for every key,
including absent keys, arbitrary duplicates and every bit distribution. -/
theorem lookup_build (bit : Key → Nat → Bool) (key : Key)
    (position fuel : Nat) (input : List (Key × Value)) :
    lookup bit key (build bit position fuel input) = lastValue key input := by
  induction fuel generalizing position input with
  | zero => cases input <;> rfl
  | succ fuel ih =>
      cases input with
      | nil => rfl
      | cons entry rest =>
          change lookup bit key (join position _ _) = _
          rw [lookup_join]
          · rw [ih, ih,
              lastValue_filter key _ (fun k => bit k position),
              lastValue_filter key _ (fun k => !bit k position)]
            cases bit key position <;> simp
          · intro selected
            rw [ih, lastValue_filter key _ (fun k => !bit k position)]
            simp [selected]
          · intro selected
            rw [ih, lastValue_filter key _ (fun k => bit k position)]
            simp [selected]

def height : Index Key Value → Nat
  | .empty | .bucket _ => 0
  | .branch _ zero one => 1 + max (height zero) (height one)

theorem height_join (position : Nat) (zero one : Index Key Value) :
    height (join position zero one) ≤ 1 + max (height zero) (height one) := by
  cases zero <;> cases one <;> simp [join, height] <;> omega

theorem height_build (bit : Key → Nat → Bool) (position fuel : Nat)
    (input : List (Key × Value)) : height (build bit position fuel input) ≤ fuel := by
  induction fuel generalizing position input with
  | zero => cases input <;> simp [build, height]
  | succ fuel ih =>
      cases input with
      | nil => simp [build, height]
      | cons entry rest =>
          change height (join position _ _) ≤ _
          apply Nat.le_trans (height_join _ _ _)
          have left := ih (position + 1) ((entry :: rest).filter fun e => !bit e.1 position)
          have right := ih (position + 1) ((entry :: rest).filter fun e => bit e.1 position)
          omega

def leaves : Index Key Value → Nat
  | .empty => 0
  | .bucket _ => 1
  | .branch _ zero one => leaves zero + leaves one

theorem leaves_join (position : Nat) (zero one : Index Key Value) :
    leaves (join position zero one) = leaves zero + leaves one := by
  cases zero <;> cases one <;> simp [join, leaves]

theorem filter_length_sum (keep : Key × Value → Bool) (input : List (Key × Value)) :
    (input.filter fun entry => !keep entry).length + (input.filter keep).length =
      input.length := by
  induction input with
  | nil => rfl
  | cons entry rest ih => cases h : keep entry <;> simp [List.filter_cons, h] <;> omega

theorem leaves_build (bit : Key → Nat → Bool) (position fuel : Nat)
    (input : List (Key × Value)) : leaves (build bit position fuel input) ≤ input.length := by
  induction fuel generalizing position input with
  | zero => cases input <;> simp [build, leaves]
  | succ fuel ih =>
      cases input with
      | nil => simp [build, leaves]
      | cons entry rest =>
          change leaves (join position _ _) ≤ _
          rw [leaves_join]
          have left := ih (position + 1) ((entry :: rest).filter fun e => !bit e.1 position)
          have right := ih (position + 1) ((entry :: rest).filter fun e => bit e.1 position)
          have total := filter_length_sum (fun e => bit e.1 position) (entry :: rest)
          omega

/-- Aggregate record visits for partitioning plus one final leaf pass.
This is a source-model cost, not a target evaluator clock. -/
def buildVisits (bit : Key → Nat → Bool) (position : Nat) :
    Nat → List (Key × Value) → Nat
  | 0, input => input.length
  | fuel + 1, input =>
      input.length +
        buildVisits bit (position + 1) fuel (input.filter fun entry => !bit entry.1 position) +
        buildVisits bit (position + 1) fuel (input.filter fun entry => bit entry.1 position)

theorem buildVisits_bound (bit : Key → Nat → Bool) (position fuel : Nat)
    (input : List (Key × Value)) :
    buildVisits bit position fuel input ≤ (fuel + 1) * input.length := by
  induction fuel generalizing position input with
  | zero => simp [buildVisits]
  | succ fuel ih =>
      rw [buildVisits]
      have left := ih (position + 1) (input.filter fun e => !bit e.1 position)
      have right := ih (position + 1) (input.filter fun e => bit e.1 position)
      have total := filter_length_sum (fun e => bit e.1 position) input
      have paid : (fuel + 1) * (input.filter fun e => !bit e.1 position).length +
          (fuel + 1) * (input.filter fun e => bit e.1 position).length =
          (fuel + 1) * input.length := by rw [← Nat.mul_add, total]
      have expand : (fuel + 1 + 1) * input.length =
          input.length + (fuel + 1) * input.length := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      omega

end InitECandidate.Solver.WitnessRadix

#print axioms InitECandidate.Solver.WitnessRadix.lookup_build
#print axioms InitECandidate.Solver.WitnessRadix.height_build
#print axioms InitECandidate.Solver.WitnessRadix.leaves_build
#print axioms InitECandidate.Solver.WitnessRadix.buildVisits_bound
