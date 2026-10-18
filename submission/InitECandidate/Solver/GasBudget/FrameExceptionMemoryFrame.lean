import InitECandidate.Solver.GasBudget.FrameExceptionMemory

namespace InitECandidate.Solver.GasBudget.FrameException
open Flapjack
open WitnessRadix

def writeOffsets : List Nat := [64, 72, 120, 128, 160, 184, 192]

theorem memory_after_away (memory : Memory) (frame continuation err empty gas spill reservoir address : BitVec 64)
    (apart : ∀ offset ∈ writeOffsets, address ≠ frame + BitVec.ofNat 64 offset)
    (notDone : address ≠ continuation + 32#64) :
    memoryAfter memory frame continuation err empty gas spill reservoir address = memory address := by
  have not64 := apart 64 (by simp [writeOffsets])
  have not72 := apart 72 (by simp [writeOffsets])
  have not120 := apart 120 (by simp [writeOffsets])
  have not128 := apart 128 (by simp [writeOffsets])
  have not160 := apart 160 (by simp [writeOffsets])
  have not184 := apart 184 (by simp [writeOffsets])
  have not192 := apart 192 (by simp [writeOffsets])
  have refillKept : WordWrites.write memory (Refill.writes frame gas spill reservoir) address = memory address :=
    WordWrites.write_away memory _ address (by simp [Refill.writes, not64, not72, not192])
  unfold memoryAfter
  rw [StoreWord.put, if_neg notDone]
  unfold choiceMemory
  split
  · rw [StoreWord.put, if_neg not160]
    exact refillKept
  · unfold clearMemory
    rw [StoreWord.put, if_neg not128, StoreWord.put, if_neg not120]
    rw [WordWrites.write_away _ _ address (by simp [Halt.writes, not64, not160, not184])]
    exact refillKept

/-- The actual handler's word-level model retains or increases used gas.
Refill only redistributes liquid/spill; a regular error then burns liquid.
The current cap supplies every natural no-wrap condition. -/
theorem memory_after_used (memory : Memory) (frame continuation err empty gas spill reservoir : BitVec 64)
    (gasCell : memory (frame + 64#64) = .word gas) (spillCell : memory (frame + 192#64) = .word spill)
    (notDone : frame + 184#64 ≠ continuation + 32#64)
    (cap : regularBudget memory frame ≤ 16777216) :
    (wordAt memory (frame + 184#64)).toNat ≤
      (wordAt (memoryAfter memory frame continuation err empty gas spill reservoir) (frame + 184#64)).toNat := by
  let refilled := WordWrites.write memory (Refill.writes frame gas spill reservoir)
  have sameUsed : refilled (frame + 184#64) = memory (frame + 184#64) :=
    WordWrites.write_away memory _ _ (by simp [Refill.writes, offsets_ne frame 184#64 64#64 (by decide),
      offsets_ne frame 184#64 72#64 (by decide), offsets_ne frame 184#64 192#64 (by decide)])
  have distinct : ((Refill.writes frame gas spill reservoir).map Prod.fst).Nodup := by
    simp [Refill.writes, offsets_ne frame 64#64 72#64 (by decide), offsets_ne frame 64#64 192#64 (by decide), offsets_ne frame 72#64 192#64 (by decide)]
  have refillGas : refilled (frame + 64#64) = .word (gas + spill) :=
    WordWrites.write_unique memory _ (frame + 64#64, gas + spill) distinct (by simp [Refill.writes])
  have numbers := cap
  simp only [regularBudget, wordAt, gasCell, spillCell, MemoryBytes.wordBits] at numbers
  change gas.toNat + (wordAt memory (frame + 184#64)).toNat + spill.toNat ≤ 16777216 at numbers
  have gasFits : gas.toNat + spill.toNat < 2^64 := by omega
  have gasNumber : (wordAt refilled (frame + 64#64)).toNat = gas.toNat + spill.toNat := by
    simp only [wordAt, refillGas, MemoryBytes.wordBits, BitVec.toNat_add_of_lt gasFits]
  have usedNumber : (wordAt refilled (frame + 184#64)).toNat = (wordAt memory (frame + 184#64)).toNat := by
    simp only [wordAt, sameUsed]
  have fits : (wordAt refilled (frame + 184#64)).toNat + (wordAt refilled (frame + 64#64)).toNat < 2^64 := by
    rw [gasNumber, usedNumber]
    omega
  have afterDone : memoryAfter memory frame continuation err empty gas spill reservoir (frame + 184#64) =
      choiceMemory refilled frame err empty (frame + 184#64) := by
    unfold memoryAfter
    rw [StoreWord.put, if_neg notDone]
  by_cases same : err = 1#64
  · have cell : choiceMemory refilled frame err empty (frame + 184#64) = memory (frame + 184#64) := by
      rw [choiceMemory, if_pos same, StoreWord.put, if_neg (offsets_ne frame 184#64 160#64 (by decide))]
      exact sameUsed
    simp only [wordAt, afterDone, cell]
    exact le_rfl
  · have haltDistinct : ((Halt.writes frame (wordAt refilled (frame + 64#64)) (wordAt refilled (frame + 184#64)) err).map Prod.fst).Nodup := by
      simp [Halt.writes, offsets_ne frame 184#64 64#64 (by decide), offsets_ne frame 184#64 160#64 (by decide), offsets_ne frame 64#64 160#64 (by decide)]
    have halted := WordWrites.write_unique refilled (Halt.writes frame (wordAt refilled (frame + 64#64)) (wordAt refilled (frame + 184#64)) err)
      (frame + 184#64, wordAt refilled (frame + 184#64) + wordAt refilled (frame + 64#64)) haltDistinct (by simp [Halt.writes])
    have cell : choiceMemory refilled frame err empty (frame + 184#64) =
        .word (wordAt refilled (frame + 184#64) + wordAt refilled (frame + 64#64)) := by
      rw [choiceMemory, if_neg same, clearMemory, StoreWord.put, if_neg (offsets_ne frame 184#64 128#64 (by decide)),
        StoreWord.put, if_neg (offsets_ne frame 184#64 120#64 (by decide))]
      exact halted
    have afterWord : wordAt (memoryAfter memory frame continuation err empty gas spill reservoir) (frame + 184#64) =
        wordAt refilled (frame + 184#64) + wordAt refilled (frame + 64#64) := by
      change MemoryBytes.wordBits (memoryAfter memory frame continuation err empty gas spill reservoir (frame + 184#64)) = _
      rw [afterDone, cell]
      rfl
    rw [afterWord, BitVec.toNat_add_of_lt fits, usedNumber]
    omega

end InitECandidate.Solver.GasBudget.FrameException

#print axioms InitECandidate.Solver.GasBudget.FrameException.memory_after_away
#print axioms InitECandidate.Solver.GasBudget.FrameException.memory_after_used
