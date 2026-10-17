import InitECandidate.Solver.WitnessRadix.CopyByteFrame
import InitECandidate.Solver.WitnessRadix.ZeroLoopTail

namespace InitECandidate.Solver.WitnessRadix.CopyBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def test (tail : Bool) (step : Nat) : ExpHOL 64 :=
  if tail then .cmp .lower (localVar "i") (localVar "n") else Copy32.condition (BitVec.ofNat 64 step)

theorem test_read {F : Type} (source : PanSemStateFiniteExact 64 F) (tail : Bool) (step index length : Nat)
    (small : length + 32 < 2 ^ 64) (ordered : index ≤ length) (stepBound : step ≤ 32) (tailStep : tail = true → step = 1)
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))) :
    @evalHOLFinite 64 F _ source (fun address => Classical.propDecidable (source.memaddrs address)) (test tail step) =
      some (.val (.word (if index + step ≤ length then 1#64 else 0#64))) := by
  cases tail with
  | false => exact Zero.condition_read source index length step small ordered stepBound indexLocal lengthLocal
  | true =>
    have stepOne := tailStep rfl
    have run := Zero.tail_condition source index length (by omega) ordered indexLocal lengthLocal
    have eq : index < length ↔ index + step ≤ length := by omega
    simpa only [test, ↓reduceIte, eq] using run

def walk {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index step : Nat) (offsets : List Nat) :
    Nat → PanSemStateFiniteExact 64 F
  | 0 => source
  | rounds + 1 => walk (advance (decClockHOLFinite source) src dst (BitVec.ofNat 64 index) offsets (BitVec.ofNat 64 step))
      src dst (index + step) step offsets rounds

/-- Both actual byte-copy loops terminate from mapped source/destination
cells, without an assumed successful load or body execution. -/
theorem loop_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (tail : Bool)
    (step index length rounds : Nat) (offsets : List Nat)
    (positive : 0 < step) (stepBound : step ≤ 32) (tailStep : tail = true → step = 1)
    (offsetBound : ∀ offset ∈ offsets, offset < step)
    (small : length + 32 < 2 ^ 64) (lower : index + step * rounds ≤ length) (upper : length < index + step * (rounds + 1))
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))))
    (sourceMapped : ∀ offset, index ≤ offset → offset < length → source.memaddrs
      (panByteAlignHOL (width := 64) (byteAddress src offset)))
    (destinationMapped : ∀ offset, index ≤ offset → offset < length → source.memaddrs
      (panByteAlignHOL (width := 64) (byteAddress dst offset)))
    (enough : rounds ≤ source.clock) :
    evaluateHOLFiniteState source (.while (test tail step) (stores offsets (increment (BitVec.ofNat 64 step)))) =
      (none, walk source src dst index step offsets rounds) := by
  classical
  induction rounds generalizing source index with
  | zero =>
    have testRun := test_read source tail step index length small (by omega) stepBound tailStep indexLocal lengthLocal
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
        simpa only [entry, decClockHOLFinite, byteAddress, BitVec.ofNat_add, BitVec.add_assoc] using h)
      (by
        intro offset member
        have h := destinationMapped (index + offset) (by omega) (by have := offsetBound offset member; omega)
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
    have tailRun := ih next (index + step) (by omega) (by simp only [Nat.mul_succ]; omega) nextSrc nextDst nextIndex nextLength
      (by intro offset low high; rw [nextMapped]; exact sourceMapped offset (by omega) high)
      (by intro offset low high; rw [nextMapped]; exact destinationMapped offset (by omega) high)
      (by rw [nextClock]; omega)
    have testRun := test_read source tail step index length small (by omega) stepBound tailStep indexLocal lengthLocal
    simp only [if_pos active] at testRun
    rw [evaluateHOLFiniteState_while_total, testRun]
    simp only []
    simp only [show (1#64 : BitVec 64) ≠ (0 : BitVec 64) from by decide, ↓reduceIte, if_neg nonzero]
    rw [bodyRun, StateSteps.fixed_clock entry next none (by rw [nextClock]; exact Nat.le_refl _)]
    exact tailRun

end InitECandidate.Solver.WitnessRadix.CopyBytes

#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.test_read
#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.loop_execute
