import InitECandidate.Solver.Input.CounterStrideLoop
import InitECandidate.Solver.Input.ByteStoreLocal
import InitECandidate.Solver.Input.ByteStoreClock
import InitECandidate.Solver.WitnessRadix.CopyWordProgram
import InitECandidate.Solver.WitnessRadix.ZeroConditions
import InitECandidate.Solver.WitnessRadix.ZeroLoopTail

namespace InitECandidate.Solver.Input.Copy32Flow
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Only actual fallthrough advances the copy counter. Failed reads and
writes are allowed and spend no source call/loop ticks. -/
structure Block (code) (body : ProgHOL 64) (stride : Nat) : Prop where
  advance : CounterFlow.Advances (ofString "i") stride body
  summary : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory, LocalSummary (ofString "n") body source
  quiet : QuietClock.Preserves code body

theorem increment (code) (stride : Nat) : Block code (CopyBytes.increment (BitVec.ofNat 64 stride)) stride :=
  ⟨CounterFlow.increment_by _ stride, (LocalPrefix.assign _ _ (by decide)).summary_full, QuietClock.assign code _ _⟩

theorem word_stores (code) (offsets : List Nat) (tail : ProgHOL 64) (stride : Nat)
    (next : Block code tail stride) : Block code (CopyWords.stores offsets tail) stride := by
  induction offsets with
  | nil => exact next
  | cons offset rest ih =>
    refine ⟨?_, ?_, QuietClock.sequence code _ _ (QuietClock.store code _ _) ih.quiet⟩
    · simpa only [Nat.zero_add, CopyWords.stores, Copy32.wordStore] using CounterFlow.sequence (ofString "i") _ _ 0 stride
        (CounterFlow.preserved _ _ (LocalPrefix.store _ _)) ih.advance
    · intro source
      exact local_summary_sequence _ _ _ (LocalPrefix.store _ _).summary_full ih.summary source

theorem byte_stores (code) (offsets : List Nat) (tail : ProgHOL 64) (stride : Nat)
    (next : Block code tail stride) : Block code (CopyBytes.stores offsets tail) stride := by
  induction offsets with
  | nil => exact next
  | cons offset rest ih =>
    refine ⟨?_, ?_, QuietClock.sequence code _ _ (QuietClock.store_byte code _ _) ih.quiet⟩
    · simpa only [Nat.zero_add, CopyBytes.stores, CopyBytes.store] using CounterFlow.sequence (ofString "i") _ _ 0 stride
        (CounterFlow.byte_store _ _ _) ih.advance
    · intro source
      exact local_summary_sequence _ _ _ (byte_store_local _ _ _) ih.summary source

theorem condition_reads (stride : Nat) (bounded : stride ≤ 32) :
    CounterFlow.StrideReads (Copy32.condition (BitVec.ofNat 64 stride)) stride 32 := by
  intro source word cell limit inside
  have typed : word = BitVec.ofNat 64 word.toNat := by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [typed] at cell
  exact Zero.condition_read source word.toNat 32 stride (by decide) inside bounded cell limit

theorem tail_reads : CounterFlow.StrideReads (.cmp .lower (localVar "i") (localVar "n")) 1 32 := by
  intro source word cell limit inside
  have typed : word = BitVec.ofNat 64 word.toNat := by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [typed] at cell
  have read := Zero.tail_condition source word.toNat 32 (by decide) inside cell limit
  simpa only [show (word.toNat < 32) = (word.toNat + 1 ≤ 32) from propext (by omega)] using read

theorem tail_block (code) : Block code CopyBytes.tailBody 1 := by
  change Block code (CopyBytes.stores [0] (CopyBytes.increment 1#64)) 1
  exact byte_stores code _ _ 1 (increment code 1)

end InitECandidate.Solver.Input.Copy32Flow

#print axioms InitECandidate.Solver.Input.Copy32Flow.word_stores
#print axioms InitECandidate.Solver.Input.Copy32Flow.byte_stores
#print axioms InitECandidate.Solver.Input.Copy32Flow.condition_reads
#print axioms InitECandidate.Solver.Input.Copy32Flow.tail_reads
#print axioms InitECandidate.Solver.Input.Copy32Flow.tail_block
