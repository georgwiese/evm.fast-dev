import InitECandidate.Solver.WitnessRadix.ZeroConditions

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def stateWord {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (index : Nat) : Nat → PanSemStateFiniteExact 64 F
  | 0 => source
  | blocks + 1 => stateWord (wordPost (decClockHOLFinite source) dst (BitVec.ofNat 64 index)) dst (index + 8) blocks

theorem loopWord_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (index length blocks : Nat) (small : length + 32 < 2 ^ 64) (aligned : index % 8 = 0)
    (fits : index + 8 * blocks ≤ length) (stop : length < index + 8 * blocks + 8)
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))))
    (mapped : ∀ offset, index ≤ offset → offset + 8 ≤ length → offset % 8 = 0 → source.memaddrs (byteAddress dst offset))
    (enough : blocks ≤ source.clock) :
    evaluateHOLFiniteState source loopWord = (none, stateWord source dst index blocks) := by
  classical
  induction blocks generalizing source index with
  | zero =>
    have test := condition_read source index length 8 small (by omega) (by decide) indexLocal lengthLocal
    have inactive : ¬ index + 8 ≤ length := by omega
    simp only [if_neg inactive] at test
    rw [loopWord_shape, evaluateHOLFiniteState_while_total, test]
    simp [stateWord]
  | succ blocks ih =>
    have active : index + 8 ≤ length := by omega
    have positive : source.clock ≠ 0 := by omega
    let entry := decClockHOLFinite source
    let next := wordPost entry dst (BitVec.ofNat 64 index)
    have blockMapped : entry.memaddrs (dst + BitVec.ofNat 64 index) :=
      mapped index (Nat.le_refl _) active aligned
    have bodyRun := blockWord_execute entry dst (BitVec.ofNat 64 index) dstLocal indexLocal blockMapped
    have nextIndex : next.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index + 8)))) := by
      change (bind _ "i" _).locals.lookup (ofString "i") = _
      rw [bind_lookup_same, BitVec.ofNat_add_ofNat index 8]
    have nextDst : next.locals.lookup (ofString "dst") = some (.val (.word dst)) := by
      unfold next wordPost
      rw [bind_lookup_other _ "i" "dst" _ (by decide)]
      exact dstLocal
    have nextLength : next.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))) := by
      unfold next wordPost
      rw [bind_lookup_other _ "i" "n" _ (by decide)]
      exact lengthLocal
    have tailRun := ih next (index + 8) (by omega) (by omega) (by omega)
      nextDst nextIndex nextLength (by
        intro offset low high aligned; exact mapped offset (by omega) high aligned)
      (by change blocks ≤ source.clock - 1; omega)
    have test := condition_read source index length 8 small (by omega) (by decide) indexLocal lengthLocal
    simp only [if_pos active] at test
    rw [loopWord_shape, evaluateHOLFiniteState_while_total, test]
    simp only []
    rw [if_pos (show (1#64 : BitVec 64) ≠ (0 : BitVec 64) from by decide)]
    simp only [if_neg positive]
    change evaluateHOLFiniteState (decClockHOLFinite source) blockWord = (none, next) at bodyRun
    rw [bodyRun]
    rw [StateSteps.fixed_clock entry next none (Nat.le_refl _)]
    change evaluateHOLFiniteState next (.while (condition 8#64) blockWord) = _
    rw [← loopWord_shape]
    exact tailRun

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.loopWord_execute
