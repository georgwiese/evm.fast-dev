import InitECandidate.Solver.WitnessRadix.Space

/-! Stable radix partition with explicit writes to two disjoint output buffers.
Addresses here are natural-number element indices. Word-address encoding and
the fixed guest's memory domain must be connected separately. -/
namespace InitECandidate.Solver.WitnessRadix

variable {Entry : Type}

abbrev BufferMemory (Entry : Type) := Nat → Option Entry

def put (memory : BufferMemory Entry) (address : Nat) (entry : Entry) : BufferMemory Entry :=
  fun query => if query = address then some entry else memory query

def writeBlock (memory : BufferMemory Entry) (start : Nat) :
    List Entry → BufferMemory Entry
  | [] => memory
  | entry :: rest => writeBlock (put memory start entry) (start + 1) rest

theorem writeBlock_outside (memory : BufferMemory Entry) (start : Nat) (input : List Entry)
    (query : Nat) (outside : query < start ∨ start + input.length ≤ query) :
    writeBlock memory start input query = memory query := by
  induction input generalizing memory start with
  | nil => rfl
  | cons entry rest ih =>
      rw [writeBlock, ih]
      · have different : query ≠ start := by simp only [List.length_cons] at outside; omega
        simp [put, different]
      · simp only [List.length_cons] at outside
        omega

theorem writeBlock_at (memory : BufferMemory Entry) (start : Nat) (input : List Entry)
    (index : Nat) (inside : index < input.length) :
    writeBlock memory start input (start + index) = input[index]? := by
  induction input generalizing memory start index with
  | nil => simp at inside
  | cons entry rest ih =>
      cases index with
      | zero =>
          rw [writeBlock, writeBlock_outside]
          · simp [put]
          · exact Or.inl (by omega)
      | succ index =>
          have bound : index < rest.length := by simpa using inside
          have addressed : start + (index + 1) = (start + 1) + index := by omega
          simpa only [writeBlock, addressed, List.getElem?_cons_succ] using
            ih (put memory start entry) (start + 1) index bound

theorem writeBlock_get (memory : BufferMemory Entry) (start : Nat) (input : List Entry)
    (query : Nat) :
    writeBlock memory start input query =
      if start ≤ query ∧ query < start + input.length then input[query - start]?
      else memory query := by
  by_cases inside : start ≤ query ∧ query < start + input.length
  · rw [if_pos inside]
    have bound : query - start < input.length := by omega
    have addressed : start + (query - start) = query := by omega
    simpa only [addressed] using writeBlock_at memory start input (query - start) bound
  · rw [if_neg inside]
    exact writeBlock_outside memory start input query (by omega)

/-- A write outside the array commutes with populating the array. -/
theorem writeBlock_put_outside (memory : BufferMemory Entry) (start : Nat)
    (input : List Entry) (address : Nat) (entry : Entry)
    (outside : address < start ∨ start + input.length ≤ address) :
    writeBlock (put memory address entry) start input =
      put (writeBlock memory start input) address entry := by
  funext query
  rw [writeBlock_get]
  by_cases same : query = address
  · subst query
    have excluded : ¬ (start ≤ address ∧ address < start + input.length) := by omega
    simp [put, excluded]
  · simp only [put, same, ↓reduceIte]
    rw [writeBlock_get]

/-- One stable-partition pass. The zero and one cursors advance independently;
each record is written once and input order is preserved in both buffers. -/
def scatter (keep : Entry → Bool) : List Entry → BufferMemory Entry → Nat → Nat → BufferMemory Entry
  | [], memory, _, _ => memory
  | entry :: rest, memory, zeroStart, oneStart =>
      if keep entry then
        scatter keep rest (put memory oneStart entry) zeroStart (oneStart + 1)
      else
        scatter keep rest (put memory zeroStart entry) (zeroStart + 1) oneStart

/-- Exact stable output and complete frame property: the final memory equals
the two specified contiguous block writes, including all untouched addresses. -/
theorem scatter_eq_blocks (keep : Entry → Bool) (input : List Entry)
    (memory : BufferMemory Entry) (zeroStart oneStart : Nat)
    (separate : zeroStart + (input.filter fun e => !keep e).length ≤ oneStart) :
    scatter keep input memory zeroStart oneStart =
      writeBlock (writeBlock memory zeroStart (input.filter fun e => !keep e))
        oneStart (input.filter keep) := by
  induction input generalizing memory zeroStart oneStart with
  | nil => rfl
  | cons entry rest ih =>
      cases selected : keep entry with
      | false =>
          simp only [scatter, selected, Bool.false_eq_true, ↓reduceIte]
          rw [ih]
          · simp [List.filter_cons, selected, writeBlock]
          · simp [List.filter_cons, selected] at separate
            omega
      | true =>
          simp only [scatter, selected, ↓reduceIte]
          rw [ih]
          · have outside : zeroStart + (rest.filter fun e => !keep e).length ≤ oneStart := by
              simpa [List.filter_cons, selected] using separate
            rw [writeBlock_put_outside _ _ _ _ _ (Or.inr outside)]
            simp [List.filter_cons, selected, writeBlock]
          · simp [List.filter_cons, selected] at separate
            omega

theorem scatter_zero_at (keep : Entry → Bool) (input : List Entry)
    (memory : BufferMemory Entry) (zeroStart oneStart index : Nat)
    (separate : zeroStart + (input.filter fun e => !keep e).length ≤ oneStart)
    (inside : index < (input.filter fun e => !keep e).length) :
    scatter keep input memory zeroStart oneStart (zeroStart + index) =
      (input.filter fun e => !keep e)[index]? := by
  rw [scatter_eq_blocks _ _ _ _ _ separate, writeBlock_outside]
  · exact writeBlock_at memory zeroStart _ index inside
  · exact Or.inl (by omega)

theorem scatter_one_at (keep : Entry → Bool) (input : List Entry)
    (memory : BufferMemory Entry) (zeroStart oneStart index : Nat)
    (separate : zeroStart + (input.filter fun e => !keep e).length ≤ oneStart)
    (inside : index < (input.filter keep).length) :
    scatter keep input memory zeroStart oneStart (oneStart + index) =
      (input.filter keep)[index]? := by
  rw [scatter_eq_blocks _ _ _ _ _ separate]
  exact writeBlock_at _ oneStart _ index inside

end InitECandidate.Solver.WitnessRadix

#print axioms InitECandidate.Solver.WitnessRadix.writeBlock_get
#print axioms InitECandidate.Solver.WitnessRadix.scatter_eq_blocks
#print axioms InitECandidate.Solver.WitnessRadix.scatter_zero_at
#print axioms InitECandidate.Solver.WitnessRadix.scatter_one_at
