import InitECandidate.Solver.WitnessRadix.Model
import Init.Data.BitVec.Lemmas

namespace InitECandidate.Solver.WitnessRadix

variable {Key Value : Type} [DecidableEq Key]

def AgreeBelow (bit : Key → Nat → Bool) (position : Nat)
    (input : List (Key × Value)) : Prop :=
  ∀ a ∈ input, ∀ b ∈ input, ∀ i < position, bit a.1 i = bit b.1 i

def Homogeneous : Index Key Value → Prop
  | .empty => True
  | .bucket input => ∀ a ∈ input, ∀ b ∈ input, a.1 = b.1
  | .branch _ zero one => Homogeneous zero ∧ Homogeneous one

theorem homogeneous_join (position : Nat) (zero one : Index Key Value)
    (left : Homogeneous zero) (right : Homogeneous one) :
    Homogeneous (join position zero one) := by
  cases zero <;> cases one <;>
    first | exact left | exact right | exact ⟨left, right⟩

theorem agreeBelow_filter_next (bit : Key → Nat → Bool) (position : Nat)
    (input : List (Key × Value)) (keep : Key × Value → Bool) (selected : Bool)
    (agree : AgreeBelow bit position input)
    (uniform : ∀ entry ∈ input, keep entry = true → bit entry.1 position = selected) :
    AgreeBelow bit (position + 1) (input.filter keep) := by
  intro a ha b hb i hi
  obtain ⟨ha, hka⟩ := List.mem_filter.mp ha
  obtain ⟨hb, hkb⟩ := List.mem_filter.mp hb
  by_cases earlier : i < position
  · exact agree a ha b hb i earlier
  · have atPosition : i = position := by omega
    rw [atPosition, uniform a ha hka, uniform b hb hkb]

/-- Complete bit inspection makes every final bucket contain only one key,
regardless of multiplicity. No assumption about the distribution of keys. -/
theorem homogeneous_build (bit : Key → Nat → Bool) (width : Nat)
    (separates : ∀ a b, (∀ i < width, bit a i = bit b i) → a = b)
    (position fuel : Nat) (input : List (Key × Value))
    (complete : width ≤ position + fuel) (agree : AgreeBelow bit position input) :
    Homogeneous (build bit position fuel input) := by
  induction fuel generalizing position input with
  | zero =>
      cases input with
      | nil => trivial
      | cons entry rest =>
          intro a ha b hb
          apply separates
          intro i hi
          exact agree a ha b hb i (by omega)
  | succ fuel ih =>
      cases input with
      | nil => trivial
      | cons entry rest =>
          change Homogeneous (join position _ _)
          apply homogeneous_join
          · apply ih (position + 1) _ (by omega)
            apply agreeBelow_filter_next bit position (entry :: rest) _ false agree
            intro e _ he
            simpa using he
          · apply ih (position + 1) _ (by omega)
            apply agreeBelow_filter_next bit position (entry :: rest) _ true agree
            intro e _ he
            exact he

/-- Realized leaves retain a single last record, rather than a list of copies. -/
inductive CompactIndex (Key Value : Type) where
  | empty
  | leaf (key : Key) (value : Value)
  | branch (position : Nat) (zero one : CompactIndex Key Value)
  deriving Repr

def compact : Index Key Value → CompactIndex Key Value
  | .empty => .empty
  | .bucket input =>
      match input.getLast? with
      | none => .empty
      | some (key, value) => .leaf key value
  | .branch position zero one => .branch position (compact zero) (compact one)

def fastLookup (bit : Key → Nat → Bool) (key : Key) : CompactIndex Key Value → Option Value
  | .empty => none
  | .leaf stored value => if stored = key then some value else none
  | .branch position zero one =>
      if bit key position then fastLookup bit key one else fastLookup bit key zero

theorem lastValue_uniform (key stored : Key) (input : List (Key × Value))
    (uniform : ∀ entry ∈ input, entry.1 = stored) :
    lastValue key input =
      if stored = key then input.getLast?.map Prod.snd else none := by
  induction input with
  | nil => simp [lastValue]
  | cons entry rest ih =>
      have head : entry.1 = stored := uniform entry (by simp)
      have tail : ∀ e ∈ rest, e.1 = stored := fun e h => uniform e (by simp [h])
      have restEq := ih tail
      cases rest with
      | nil => simp [lastValue, head]
      | cons next rest =>
          cases last : (next :: rest).getLast? with
          | none => simp at last
          | some found =>
              rw [lastValue, restEq, List.getLast?_cons_cons, last]
              by_cases equal : stored = key <;> simp [head, equal]

theorem fastLookup_compact (bit : Key → Nat → Bool) (key : Key)
    (index : Index Key Value) (valid : Homogeneous index) :
    fastLookup bit key (compact index) = lookup bit key index := by
  induction index with
  | empty => rfl
  | bucket input =>
      cases last : input.getLast? with
      | none =>
          have empty : input = [] := by simpa using last
          subst input
          rfl
      | some found =>
          have uniform : ∀ e ∈ input, e.1 = found.1 := fun e h =>
            valid e h found (List.mem_of_getLast? last)
          simp only [compact, last, fastLookup, lookup]
          rw [lastValue_uniform key found.1 input uniform, last]
          rfl
  | branch position zero one ihZero ihOne =>
      simp only [Homogeneous] at valid
      simp only [compact, fastLookup, lookup]
      rw [ihZero valid.1, ihOne valid.2]

def compactHeight : CompactIndex Key Value → Nat
  | .empty | .leaf _ _ => 0
  | .branch _ zero one => 1 + max (compactHeight zero) (compactHeight one)

theorem compactHeight_le (index : Index Key Value) :
    compactHeight (compact index) ≤ height index := by
  induction index with
  | empty => exact Nat.le_refl _
  | bucket input => cases h : input.getLast? <;> simp [compact, h, compactHeight, height]
  | branch position zero one ihZero ihOne =>
      simp only [compact, compactHeight, height]
      omega

/-- Number of inspected index nodes, including one terminal leaf/empty test.
Key comparison and address-level operation costs must be priced separately. -/
def queryVisits (bit : Key → Nat → Bool) (key : Key) : CompactIndex Key Value → Nat
  | .empty | .leaf _ _ => 1
  | .branch position zero one =>
      1 + if bit key position then queryVisits bit key one else queryVisits bit key zero

theorem queryVisits_bound (bit : Key → Nat → Bool) (key : Key)
    (index : CompactIndex Key Value) : queryVisits bit key index ≤ compactHeight index + 1 := by
  induction index with
  | empty | leaf => simp [queryVisits, compactHeight]
  | branch position zero one ihZero ihOne =>
      simp only [queryVisits, compactHeight]
      cases bit key position <;> simp <;> omega

/-- Fixed-width, duplicate-preserving immutable index. -/
def buildIndex (bit : Key → Nat → Bool) (width : Nat)
    (input : List (Key × Value)) : CompactIndex Key Value := compact (build bit 0 width input)

theorem fastLookup_buildIndex (bit : Key → Nat → Bool) (width : Nat)
    (separates : ∀ a b, (∀ i < width, bit a i = bit b i) → a = b)
    (input : List (Key × Value)) (key : Key) :
    fastLookup bit key (buildIndex bit width input) = lastValue key input := by
  rw [buildIndex, fastLookup_compact, lookup_build]
  apply homogeneous_build bit width separates 0 width input (by omega)
  intro _ _ _ _ _ impossible
  omega

theorem queryVisits_buildIndex (bit : Key → Nat → Bool) (width : Nat)
    (input : List (Key × Value)) (key : Key) :
    queryVisits bit key (buildIndex bit width input) ≤ width + 1 := by
  apply Nat.le_trans (queryVisits_bound _ _ _)
  have bounded := height_build bit 0 width input
  have compressed := compactHeight_le (build bit 0 width input)
  dsimp only [buildIndex]
  omega

/-- Instantiation for the actual 32-byte hash width. -/
theorem hash_lookup (input : List (BitVec 256 × Value)) (key : BitVec 256) :
    fastLookup BitVec.getLsbD key (buildIndex BitVec.getLsbD 256 input) =
      lastValue key input :=
  fastLookup_buildIndex BitVec.getLsbD 256
    (fun _ _ same => BitVec.eq_of_getLsbD_eq same) input key

theorem hash_query_visits (input : List (BitVec 256 × Value)) (key : BitVec 256) :
    queryVisits BitVec.getLsbD key (buildIndex BitVec.getLsbD 256 input) ≤ 257 :=
  queryVisits_buildIndex BitVec.getLsbD 256 input key

end InitECandidate.Solver.WitnessRadix

#print axioms InitECandidate.Solver.WitnessRadix.fastLookup_buildIndex
#print axioms InitECandidate.Solver.WitnessRadix.queryVisits_buildIndex
#print axioms InitECandidate.Solver.WitnessRadix.hash_lookup
#print axioms InitECandidate.Solver.WitnessRadix.hash_query_visits
