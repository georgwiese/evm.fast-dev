import InitECandidate.Solver.Mpt.KeyToNibblesBlock
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Control

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem Ready.with_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64)
    (index written clock : Nat) (bytes : Nat → BitVec 8) (ready : Ready source key out index written bytes) :
    Ready {source with clock := clock} key out index written bytes :=
  ⟨ready.keyCell, ready.outCell, ready.indexCell, ready.lengthCell, ready.little, ready.inside,
    ready.fits, ready.mapped, ready.input, ready.separate, ready.nibbles⟩

theorem block_condition_read {F : Type} (source : PanSemStateFiniteExact 64 F) (index : Nat)
    (inside : index ≤ 32)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (lengthCell : source.locals.lookup (ofString "n") = some (.val (.word 32#64))) :
    eval source blockCondition = some (.val (.word (if index + 4 ≤ 32 then 1#64 else 0#64))) := by
  have indexNumber : (BitVec.ofNat 64 index).toNat = index := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have addition : (BitVec.ofNat 64 index + 4#64).toNat = index + 4 := by
    rw [BitVec.toNat_add_of_lt (by change (BitVec.ofNat 64 index).toNat + 4 < 2^64; rw [indexNumber]; omega), indexNumber]
    rfl
  by_cases active : index + 4 ≤ 32
  · have comparison : ¬ (32#64 : BitVec 64) < BitVec.ofNat 64 index + 4#64 := by
      change ¬ 32 < (BitVec.ofNat 64 index + 4#64).toNat
      rw [addition]
      omega
    simp [blockCondition, eval, evalHOLExact, evalListHOLExact, addConst, localVar, toExact, current, lengthCell,
      valueIsWord, valueWord, wordOpHOL, wordOp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, comparison, active]
  · have comparison : (32#64 : BitVec 64) < BitVec.ofNat 64 index + 4#64 := by
      change 32 < (BitVec.ofNat 64 index + 4#64).toNat
      rw [addition]
      omega
    simp [blockCondition, eval, evalHOLExact, evalListHOLExact, addConst, localVar, toExact, current, lengthCell,
      valueIsWord, valueWord, wordOpHOL, wordOp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, comparison, active]

theorem block_loop_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (key out : BitVec 64) (index : Nat)
    (bytes : Nat → BitVec 8) (ready : Ready source key out index 0 bytes) (multiple : index % 4 = 0)
    (enough : (32 - index) / 4 ≤ source.clock) :
    ∃ post, evaluateHOLFiniteState source blockLoop = (none, post) ∧ Ready post key out 32 0 bytes ∧
      post.clock = source.clock - (32 - index) / 4 ∧ OutputFrame source post out := by
  generalize rankEq : 32 - index = rank
  induction rank using Nat.strongRecOn generalizing source index with
  | ind rank ih =>
    have inside : index ≤ 32 := by have bounded := ready.inside; omega
    have test := block_condition_read source index inside ready.indexCell ready.lengthCell
    by_cases done : index = 32
    · subst index
      have stopped : eval source blockCondition = some (.val (.word 0#64)) := by simpa using test
      have run : evaluateHOLFiniteState source blockLoop = (none, source) := by
        rw [loop_shapes.1, evaluateHOLFiniteState_while_total]
        simp only [eval, evalHOLFinite] at stopped ⊢
        rw [stopped]
        simp
      exact ⟨source, run, ready, by simp [← rankEq], OutputFrame.refl source out⟩
    · have room : index + 4 ≤ 32 := by omega
      have entering : eval source blockCondition = some (.val (.word 1#64)) := by simpa only [if_pos room] using test
      have positive : source.clock ≠ 0 := by omega
      let entry := decClockHOLFinite source
      have entryReady : Ready entry key out index 0 bytes := Ready.with_clock source key out index 0 (source.clock - 1) bytes ready
      obtain ⟨next, bodyRun, nextReady, nextClock, bodyFrame⟩ := block_execute entry key out index bytes entryReady room
      change next.clock = source.clock - 1 at nextClock
      have smaller : 32 - (index + 4) < rank := by omega
      have tailEnough : (32 - (index + 4)) / 4 ≤ next.clock := by omega
      obtain ⟨post, tailRun, finalReady, finalClock, tailFrame⟩ := ih (32 - (index + 4)) smaller next (index + 4) nextReady (by omega) tailEnough rfl
      have step : evaluateHOLFiniteState source blockLoop = evaluateHOLFiniteState next blockLoop := by
        rw [loop_shapes.1, evaluateHOLFiniteState_while_total]
        simp only [eval, evalHOLFinite] at entering ⊢
        rw [entering]
        simp only
        rw [if_pos (show (1#64 : BitVec 64) ≠ 0 from by decide), if_neg positive, bodyRun]
        simp only
        rw [StateSteps.fixed_clock entry next none (by change next.clock ≤ source.clock - 1; omega)]
      have stepFrame : OutputFrame source next out := ⟨bodyFrame.fields, bodyFrame.memory⟩
      refine ⟨post, step.trans tailRun, finalReady, ?_, OutputFrame.trans source next post out stepFrame tailFrame⟩
      rw [finalClock, nextClock]
      omega

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.Ready.with_clock
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.block_condition_read
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.block_loop_execute
