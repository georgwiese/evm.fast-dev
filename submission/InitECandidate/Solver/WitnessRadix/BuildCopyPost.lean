import InitECandidate.Solver.WitnessRadix.BuildCopyLoop

namespace InitECandidate.Solver.WitnessRadix.BuildCopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem copyState_other {F : Type} (source : PanSemStateFiniteExact 64 F)
    (src start : BitVec 64) (index : Nat) (input : List (BitVec 64)) (name : MlS)
    (notI : ofString "i" ≠ name) :
    (copyState source src start index input).locals.lookup name = source.locals.lookup name := by
  induction input generalizing source index with
  | nil => rfl
  | cons value rest ih =>
      rw [copyState, ih]
      simp [QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, notI]

theorem copyState_index {F : Type} (source : PanSemStateFiniteExact 64 F)
    (src start : BitVec 64) (index : Nat) (input : List (BitVec 64))
    (initial : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index)))) :
    (copyState source src start index input).locals.lookup (ofString "i") =
      some (.val (.word (BitVec.ofNat 64 (index + input.length)))) := by
  induction input generalizing source index with
  | nil => simpa only [copyState, List.length_nil, Nat.add_zero] using initial
  | cons value rest ih =>
      rw [copyState]
      let nextState := (bind { source with
          clock := source.clock - 1
          memory := StoreWord.put source.memory (row src start (BitVec.ofNat 64 index)) value }
        "i" (BitVec.ofNat 64 (index + 1)))
      have next := ih nextState (index + 1) (by
        simp [nextState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE])
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 rest.length] using next

theorem copyState_frame {F : Type} (source : PanSemStateFiniteExact 64 F)
    (src start : BitVec 64) (index : Nat) (input : List (BitVec 64)) :
    emptyLocalsHOLFinite (copyState source src start index input) =
      emptyLocalsHOLFinite { source with
        clock := source.clock - input.length
        memory := copyMemory source.memory src start index input } := by
  induction input generalizing source index with
  | nil => simp [copyState, copyMemory]
  | cons value rest ih =>
      rw [copyState, ih]
      have clockSub : source.clock - 1 - rest.length = source.clock - (value :: rest).length := by
        simp only [List.length_cons]
        omega
      simp only [QueryBranch.bind, setVarHOLFinite, copyMemory, emptyLocalsHOLFinite, clockSub]

theorem row_address (base start : BitVec 64) (index : Nat) :
    row base start (BitVec.ofNat 64 index) = byteAddress base (8 * (start.toNat + index)) := by
  have startEq : start = BitVec.ofNat 64 start.toNat := by simp
  rw [row, startEq, ← BitVec.ofNat_add]
  change base + (BitVec.ofNat 64 (start.toNat + index) * BitVec.ofNat 64 8) = _
  rw [← BitVec.ofNat_mul]
  simp only [byteAddress, Nat.mul_comm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt start.isLt]

theorem rows_injective (base start : BitVec 64) (limit left right : Nat)
    (allocation : base.toNat + 8 * (start.toNat + limit) < 2 ^ 64)
    (leftInside : left < limit) (rightInside : right < limit) (different : left ≠ right) :
    row base start (BitVec.ofNat 64 left) ≠ row base start (BitVec.ofNat 64 right) := by
  rw [row_address, row_address]
  apply byteAddress_ne <;> omega

/-- The complete copy poststate contains precisely the supplied ordinals in
the destination interval. Distinct destination words follow from no wrap. -/
theorem copied_rows (memory : BitVec 64 → HolWordLab 64) (domain : BitVec 64 → Prop)
    (base start : BitVec 64) (index : Nat) (input : List (BitVec 64))
    (allocation : base.toNat + 8 * (start.toNat + index + input.length) < 2 ^ 64)
    (mapped : ∀ offset < input.length, domain (row base start (BitVec.ofNat 64 (index + offset)))) :
    Rows (copyMemory memory base start index input) domain base start index input := by
  induction input generalizing memory index with
  | nil => trivial
  | cons value rest ih =>
      change domain (row base start (BitVec.ofNat 64 index)) ∧ _ ∧ _
      refine ⟨by simpa using mapped 0 (by simp), ?_, ?_⟩
      · rw [copyMemory, copyMemory_away]
        · simp [StoreWord.put]
        · intro offset inside
          apply rows_injective base start (index + (value :: rest).length) index (index + 1 + offset)
          · simp only [List.length_cons] at allocation ⊢
            omega
          · simp
          · simp only [List.length_cons]
            omega
          · omega
      · apply ih
        · simp only [List.length_cons] at allocation
          omega
        · intro offset inside
          have nextMapped := mapped (offset + 1) (by simp only [List.length_cons]; omega)
          simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using nextMapped

end InitECandidate.Solver.WitnessRadix.BuildCopy

#print axioms InitECandidate.Solver.WitnessRadix.BuildCopy.copyState_frame
#print axioms InitECandidate.Solver.WitnessRadix.BuildCopy.copyState_index
#print axioms InitECandidate.Solver.WitnessRadix.BuildCopy.copied_rows
