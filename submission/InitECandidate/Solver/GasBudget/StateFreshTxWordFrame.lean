import InitECandidate.Solver.GasBudget.StateFreshTxFamily

namespace InitECandidate.Solver.GasBudget.StateFreshTx
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable NaturalLayout

theorem walk_code (specs : List Spec) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start tx : Nat) :
    (walk source start tx specs).code = source.code := by
  induction specs generalizing source start with
  | nil => rfl
  | cons spec specs ih => exact ih _ _

theorem walk_counter (specs : List Spec) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start tx : Nat) :
    (walk source start tx specs).globals.lookup (ofString "journal_n") = some (.val (.word 0#64)) := by
  induction specs generalizing source start with
  | nil => exact Input.putGlobal.lookup_same _ _ _
  | cons spec specs ih => exact ih _ _

/-- A word before every new constructor survives the entire tail, provided
none of its actual transaction-record stores selects that word. -/
theorem walk_word (specs : List Spec) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (start tx : Nat)
    (lower : 2701131776 ≤ start) (aligned : start % 8 = 0)
    (wellFormed : ∀ spec ∈ specs, spec.Valid) (room : cursor start specs ≤ 33806089496)
    (address : BitVec 64) (before : address.toNat < start)
    (away : ∀ spec ∈ specs, address ≠ MemoryRegion.address ⟨tx, 72⟩ spec.offset) :
    (walk source start tx specs).memory address = source.memory address := by
  induction specs generalizing source start with
  | nil => rfl
  | cons spec specs ih =>
    have nextRoom : freshEnd spec.kind start spec.capacity ≤ 33806089496 :=
      Nat.le_trans (cursor_forward specs (freshEnd spec.kind start spec.capacity)) room
    have valid := fresh_valid spec.kind start spec.capacity (Nat.two_pow_pos _) lower nextRoom aligned
    have nextAligned : freshEnd spec.kind start spec.capacity % 8 = 0 := by
      have position := valid.aligned .position
      change ((fresh spec.kind start spec.capacity).base .position + 8 * spec.capacity) % 8 = 0
      rw [Nat.add_mod, position]
      omega
    have forward : start ≤ freshEnd spec.kind start spec.capacity := by dsimp only [freshEnd]; omega
    rw [walk, ih (source := stepState source start tx spec) (start := freshEnd spec.kind start spec.capacity)
      (by omega) nextAligned (by intro next member; exact wellFormed next (by simp [member])) room (by omega)
      (by intro next member; exact away next (by simp [member]))]
    change StoreWord.put _ _ _ address = _
    rw [StoreWord.put, if_neg (away spec (by simp))]
    exact TableRuntime.caller_memory_away source "t" spec.kind start spec.capacity valid address (Or.inl before)

theorem record_word_distinct (tx : Nat) (valid : MemoryRegion.Valid ⟨tx, 72⟩) (first second : Nat)
    (firstBound : first ≤ 72) (secondBound : second ≤ 72) (different : first ≠ second) :
    MemoryRegion.address ⟨tx, 72⟩ first ≠ MemoryRegion.address ⟨tx, 72⟩ second := by
  intro same
  have numeric := congrArg BitVec.toNat same
  rw [MemoryRegion.address_number ⟨tx, 72⟩ valid first firstBound,
    MemoryRegion.address_number ⟨tx, 72⟩ valid second secondBound] at numeric
  omega

end InitECandidate.Solver.GasBudget.StateFreshTx

#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.walk_counter
#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.walk_code
#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.walk_word
#print axioms InitECandidate.Solver.GasBudget.StateFreshTx.record_word_distinct
