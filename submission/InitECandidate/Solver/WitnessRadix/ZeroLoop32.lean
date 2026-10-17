import InitECandidate.Solver.WitnessRadix.ZeroConditions

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def state32 {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (index : Nat) : Nat → PanSemStateFiniteExact 64 F
  | 0 => source
  | blocks + 1 => state32 (blockPost (decClockHOLFinite source) dst (BitVec.ofNat 64 index)) dst (index + 32) blocks

theorem loop32_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (index length blocks : Nat) (small : length + 32 < 2 ^ 64) (aligned : index % 8 = 0)
    (fits : index + 32 * blocks ≤ length) (stop : length < index + 32 * blocks + 32)
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))))
    (mapped : ∀ offset, index ≤ offset → offset + 8 ≤ length → offset % 8 = 0 → source.memaddrs (byteAddress dst offset))
    (enough : blocks ≤ source.clock) :
    evaluateHOLFiniteState source loop32 = (none, state32 source dst index blocks) := by
  classical
  induction blocks generalizing source index with
  | zero =>
    have test := condition_read source index length 32 small (by omega) (by decide) indexLocal lengthLocal
    have inactive : ¬ index + 32 ≤ length := by omega
    simp only [if_neg inactive] at test
    rw [loop32_shape, evaluateHOLFiniteState_while_total, test]
    simp [state32]
  | succ blocks ih =>
    have active : index + 32 ≤ length := by omega
    have positive : source.clock ≠ 0 := by omega
    let entry := decClockHOLFinite source
    let next := blockPost entry dst (BitVec.ofNat 64 index)
    have blockMapped (limb : Fin 4) : entry.memaddrs
        (dst + BitVec.ofNat 64 index + BitVec.ofNat 64 (8 * limb.val)) := by
      have address : dst + BitVec.ofNat 64 index + BitVec.ofNat 64 (8 * limb.val) = byteAddress dst (index + 8 * limb.val) := by
        simp only [byteAddress, BitVec.ofNat_add, BitVec.add_assoc]
      rw [address]
      exact mapped _ (by omega) (by have := limb.isLt; omega) (by omega)
    have bodyRun := block32_execute entry dst (BitVec.ofNat 64 index) dstLocal indexLocal blockMapped
    have nextIndex : next.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index + 32)))) := by
      change (bind _ "i" _).locals.lookup (ofString "i") = _
      rw [bind_lookup_same, BitVec.ofNat_add_ofNat index 32]
    have nextDst : next.locals.lookup (ofString "dst") = some (.val (.word dst)) := by
      unfold next blockPost
      rw [bind_lookup_other _ "i" "dst" _ (by decide)]
      exact dstLocal
    have nextLength : next.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))) := by
      unfold next blockPost
      rw [bind_lookup_other _ "i" "n" _ (by decide)]
      exact lengthLocal
    have tailRun := ih next (index + 32) (by omega) (by omega) (by omega)
      nextDst nextIndex nextLength (by
        intro offset low high aligned; exact mapped offset (by omega) high aligned)
      (by change blocks ≤ source.clock - 1; omega)
    have test := condition_read source index length 32 small (by omega) (by decide) indexLocal lengthLocal
    simp only [if_pos active] at test
    rw [loop32_shape, evaluateHOLFiniteState_while_total, test]
    simp only []
    rw [if_pos (show (1#64 : BitVec 64) ≠ (0 : BitVec 64) from by decide)]
    simp only [if_neg positive]
    change evaluateHOLFiniteState (decClockHOLFinite source) block32 = (none, next) at bodyRun
    rw [bodyRun]
    rw [StateSteps.fixed_clock entry next none (Nat.le_refl _)]
    change evaluateHOLFiniteState next (.while (condition 32#64) block32) = _
    rw [← loop32_shape]
    exact tailRun

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.loop32_execute
