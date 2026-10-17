import InitECandidate.Solver.WitnessRadix.ZeroByteStore

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def stateByte {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64) (index : Nat) : Nat → PanSemStateFiniteExact 64 F
  | 0 => source
  | remaining + 1 => stateByte (bytePost (decClockHOLFinite source) dst (BitVec.ofNat 64 index)) dst (index + 1) remaining

theorem tail_condition {F : Type} (source : PanSemStateFiniteExact 64 F) (index length : Nat)
    (small : length < 2 ^ 64) (ordered : index ≤ length)
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length)))) :
    @evalHOLFinite 64 F _ source (fun address => Classical.propDecidable (source.memaddrs address))
      (.cmp .lower (localVar "i") (localVar "n")) = some (.val (.word (if index < length then 1#64 else 0#64))) := by
  have indexSmall : index < 2 ^ 64 := by omega
  simp [evalHOLFinite, evalHOLExact, toExact, localVar, indexLocal, lengthLocal,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt indexSmall]

theorem loopTail_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (dst : BitVec 64)
    (index length remaining : Nat) (small : length < 2 ^ 64) (size : index + remaining = length)
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (lengthLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))))
    (mapped : ∀ offset, index ≤ offset → offset < length → source.memaddrs
      (panByteAlignHOL (width := 64) (byteAddress dst offset)))
    (enough : remaining ≤ source.clock) :
    evaluateHOLFiniteState source loopTail = (none, stateByte source dst index remaining) := by
  classical
  induction remaining generalizing source index with
  | zero =>
    have test := tail_condition source index length small (by omega) indexLocal lengthLocal
    have inactive : ¬ index < length := by omega
    simp only [if_neg inactive] at test
    rw [other_loop_shapes.2, evaluateHOLFiniteState_while_total, test]
    simp [stateByte]
  | succ remaining ih =>
    have active : index < length := by omega
    have positive : source.clock ≠ 0 := by omega
    let entry := decClockHOLFinite source
    let next := bytePost entry dst (BitVec.ofNat 64 index)
    have bodyRun := tail_body_execute entry dst (BitVec.ofNat 64 index) dstLocal indexLocal
      (mapped index (Nat.le_refl _) active)
    have nextIndex : next.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (index + 1)))) := by
      change (bind _ "i" _).locals.lookup (ofString "i") = _
      rw [bind_lookup_same, BitVec.ofNat_add_ofNat index 1]
    have nextDst : next.locals.lookup (ofString "dst") = some (.val (.word dst)) := by
      unfold next bytePost
      rw [bind_lookup_other _ "i" "dst" _ (by decide)]
      exact dstLocal
    have nextLength : next.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))) := by
      unfold next bytePost
      rw [bind_lookup_other _ "i" "n" _ (by decide)]
      exact lengthLocal
    have tailRun := ih next (index + 1) (by omega) nextDst nextIndex nextLength
      (by intro offset low high; exact mapped offset (by omega) high)
      (by change remaining ≤ source.clock - 1; omega)
    have test := tail_condition source index length small (by omega) indexLocal lengthLocal
    simp only [if_pos active] at test
    rw [other_loop_shapes.2, evaluateHOLFiniteState_while_total, test]
    simp only []
    rw [if_pos (show (1#64 : BitVec 64) ≠ (0 : BitVec 64) from by decide)]
    simp only [if_neg positive]
    change evaluateHOLFiniteState (decClockHOLFinite source) tailBody = (none, next) at bodyRun
    rw [bodyRun, StateSteps.fixed_clock entry next none (Nat.le_refl _)]
    change evaluateHOLFiniteState next (.while (.cmp .lower (localVar "i") (localVar "n")) tailBody) = _
    rw [← other_loop_shapes.2]
    exact tailRun

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.tail_condition
#print axioms InitECandidate.Solver.WitnessRadix.Zero.loopTail_execute
