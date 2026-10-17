import InitECandidate.Solver.WitnessRadix.CopyWordFrame
import InitECandidate.Solver.WitnessRadix.CopyByteLoop

namespace InitECandidate.Solver.WitnessRadix.CopyWords
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def walk {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index step : Nat) (offsets : List Nat) :
    Nat → PanSemStateFiniteExact 64 F
  | 0 => source
  | rounds + 1 => walk (advance (decClockHOLFinite source) src dst (BitVec.ofNat 64 index) offsets (BitVec.ofNat 64 step))
      src dst (index + step) step offsets rounds

/-- The actual aligned word-copy loops terminate from mapped cells. -/
theorem loop_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (tail : Bool)
    (step index length rounds : Nat) (offsets : List Nat)
    (positive : 0 < step) (stepBound : step ≤ 32) (tailStep : tail = true → step = 1)
    (offsetBound : ∀ offset ∈ offsets, offset < step)
    (stepAligned : step % 8 = 0) (indexAligned : index % 8 = 0)
    (offsetAligned : ∀ offset ∈ offsets, offset % 8 = 0)
    (small : length + 32 < 2 ^ 64) (lower : index + step * rounds ≤ length) (upper : length < index + step * (rounds + 1))
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))))
    (sourceMapped : ∀ offset, index ≤ offset → offset < length → offset % 8 = 0 → source.memaddrs (byteAddress src offset))
    (destinationMapped : ∀ offset, index ≤ offset → offset < length → offset % 8 = 0 → source.memaddrs (byteAddress dst offset))
    (enough : rounds ≤ source.clock) :
    evaluateHOLFiniteState source (.while (CopyBytes.test tail step) (stores offsets (CopyBytes.increment (BitVec.ofNat 64 step)))) =
      (none, walk source src dst index step offsets rounds) := by
  classical
  induction rounds generalizing source index with
  | zero =>
    have testRun := CopyBytes.test_read source tail step index length small (by omega) stepBound tailStep indexLocal lengthLocal
    have inactive : ¬ index + step ≤ length := by simpa using Nat.not_le_of_gt upper
    simp only [if_neg inactive] at testRun
    rw [evaluateHOLFiniteState_while_total, testRun]
    simp [walk]
  | succ rounds ih =>
    simp only [Nat.mul_succ] at lower upper
    have active : index + step ≤ length := by omega
    have nonzero : source.clock ≠ 0 := by omega
    let entry := decClockHOLFinite source
    let next := advance entry src dst (BitVec.ofNat 64 index) offsets (BitVec.ofNat 64 step)
    have bodyRun := block_execute entry src dst (BitVec.ofNat 64 index) offsets (BitVec.ofNat 64 step)
      srcLocal dstLocal indexLocal
      (by
        intro offset member
        have h := sourceMapped (index + offset) (by omega) (by have := offsetBound offset member; omega)
          (by simp [Nat.add_mod, indexAligned, offsetAligned offset member])
        simpa only [entry, decClockHOLFinite, byteAddress, BitVec.ofNat_add, BitVec.add_assoc] using h)
      (by
        intro offset member
        have h := destinationMapped (index + offset) (by omega) (by have := offsetBound offset member; omega)
          (by simp [Nat.add_mod, indexAligned, offsetAligned offset member])
        simpa only [entry, decClockHOLFinite, byteAddress, BitVec.ofNat_add, BitVec.add_assoc] using h)
    have fields := advance_frame entry src dst (BitVec.ofNat 64 index) offsets (BitVec.ofNat 64 step)
    have nextMapped : next.memaddrs = source.memaddrs := by
      have h := congrArg (fun state : PanSemStateFiniteExact 64 F => state.memaddrs) fields
      exact h
    have nextClock : next.clock = source.clock - 1 := by
      have h := congrArg (fun state : PanSemStateFiniteExact 64 F => state.clock) fields
      exact h
    have nextIndex : next.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index + step)))) := by
      simpa only [BitVec.ofNat_add] using advance_index entry src dst (BitVec.ofNat 64 index) offsets (BitVec.ofNat 64 step)
    have nextSrc : next.locals.lookup (ofString "src") = some (.val (.word src)) := by
      rw [advance_other entry src dst (BitVec.ofNat 64 index) offsets (BitVec.ofNat 64 step) _ (by decide)]
      exact srcLocal
    have nextDst : next.locals.lookup (ofString "dst") = some (.val (.word dst)) := by
      rw [advance_other entry src dst (BitVec.ofNat 64 index) offsets (BitVec.ofNat 64 step) _ (by decide)]
      exact dstLocal
    have nextLength : next.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))) := by
      rw [advance_other entry src dst (BitVec.ofNat 64 index) offsets (BitVec.ofNat 64 step) _ (by decide)]
      exact lengthLocal
    have tailRun := ih next (index + step) (by simp [Nat.add_mod, indexAligned, stepAligned]) (by omega) (by simp only [Nat.mul_succ]; omega) nextSrc nextDst nextIndex nextLength
      (by intro offset low high aligned; rw [nextMapped]; exact sourceMapped offset (by omega) high aligned)
      (by intro offset low high aligned; rw [nextMapped]; exact destinationMapped offset (by omega) high aligned)
      (by rw [nextClock]; omega)
    have testRun := CopyBytes.test_read source tail step index length small (by omega) stepBound tailStep indexLocal lengthLocal
    simp only [if_pos active] at testRun
    rw [evaluateHOLFiniteState_while_total, testRun]
    simp only []
    simp only [show (1#64 : BitVec 64) ≠ (0 : BitVec 64) from by decide, ↓reduceIte, if_neg nonzero]
    rw [bodyRun, StateSteps.fixed_clock entry next none (by rw [nextClock]; exact Nat.le_refl _)]
    exact tailRun

end InitECandidate.Solver.WitnessRadix.CopyWords

#print axioms InitECandidate.Solver.WitnessRadix.CopyWords.loop_execute
