import InitECandidate.Solver.GasBudget.RunFramesMarked
import InitECandidate.Solver.WitnessRadix.Bindings

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- Actual memory facts selecting an immediate completion guard. Opcode
dispatch remains a separate case; no helper execution is stored. -/
inductive ImmediateDone (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame cont : BitVec 64) : Prop where
  | marked (flag : BitVec 64) (mapped : source.memaddrs (cont + 32#64))
      (stored : source.memory (cont + 32#64) = .word flag) (nonzero : flag ≠ 0#64) : ImmediateDone source frame cont
  | halted (markedMapped : source.memaddrs (cont + 32#64)) (markedStored : source.memory (cont + 32#64) = .word 0#64)
      (haltedMapped : source.memaddrs (frame + 104#64)) (haltedStored : source.memory (frame + 104#64) = .word 0#64) : ImmediateDone source frame cont
  | exhausted (active pc length : BitVec 64)
      (markedMapped : source.memaddrs (cont + 32#64)) (markedStored : source.memory (cont + 32#64) = .word 0#64)
      (activeMapped : source.memaddrs (frame + 104#64)) (activeStored : source.memory (frame + 104#64) = .word active) (activeNonzero : active ≠ 0#64)
      (pcMapped : source.memaddrs (frame + 0#64)) (pcStored : source.memory (frame + 0#64) = .word pc)
      (lengthMapped : source.memaddrs (frame + 56#64)) (lengthStored : source.memory (frame + 56#64) = .word length)
      (finished : length.toNat ≤ pc.toNat) : ImmediateDone source frame cont

theorem ImmediateDone.of_fields {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frame cont : BitVec 64}
    (ready : ImmediateDone source frame cont) (memory : target.memory = source.memory) (domain : target.memaddrs = source.memaddrs) : ImmediateDone target frame cont := by
  cases ready with
  | marked flag mapped stored nonzero => exact .marked flag (by rw [domain]; exact mapped) (by rw [memory]; exact stored) nonzero
  | halted markedMapped markedStored haltedMapped haltedStored =>
    exact .halted (by rw [domain]; exact markedMapped) (by rw [memory]; exact markedStored)
      (by rw [domain]; exact haltedMapped) (by rw [memory]; exact haltedStored)
  | exhausted active pc length markedMapped markedStored activeMapped activeStored activeNonzero pcMapped pcStored lengthMapped lengthStored finished =>
    exact .exhausted active pc length (by rw [domain]; exact markedMapped) (by rw [memory]; exact markedStored)
      (by rw [domain]; exact activeMapped) (by rw [memory]; exact activeStored) activeNonzero
      (by rw [domain]; exact pcMapped) (by rw [memory]; exact pcStored)
      (by rw [domain]; exact lengthMapped) (by rw [memory]; exact lengthStored) finished

theorem done_body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame cont : BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (continuation : source.globals.lookup (ofString "cur_cont") = some (.val (.word cont)))
    (ready : ImmediateDone source frame cont) :
    evaluateHOLFiniteState source loopBody =
      (let output := evaluateHOLFiniteState (markedState source) RootExit.selected
       (output.1, restore source "done" output.2)) := by
  cases ready with
  | marked flag mapped stored nonzero => exact marked_body_execute source cont flag continuation mapped stored nonzero
  | halted markedMapped markedStored haltedMapped haltedStored =>
    let declared := bind source "done" 0#64
    have readMarked := Input.global_field_read declared "cur_cont" cont 32#64 0#64 continuation markedMapped markedStored
    change eval declared (RootExit.recordLoad 32#64) = some (.val (.word 0#64)) at readMarked
    have testMarked : eval declared markedCondition = some (.val (.word 0#64)) := by
      simp only [eval] at readMarked
      simp [eval, markedCondition, evalHOLExact, readMarked, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have readHalted := frame_read declared frame 104#64 0#64 ev haltedMapped haltedStored
    have testHalted : eval declared haltedCondition = some (.val (.word 1#64)) := by
      simp only [eval] at readHalted
      simp [eval, haltedCondition, evalHOLExact, readHalted, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have assigned := StateSteps.assign_execute declared "done" (.const 1#64) 0#64 1#64 (bind_lookup_same _ _ _) rfl
    change evaluateHOLFiniteState declared markDone = (none, markedState source) at assigned
    have headRun : evaluateHOLFiniteState declared head = (none, markedState source) := by
      simp only [eval] at testMarked testHalted
      rw [head_shape, evaluateHOLFiniteState_ite, testMarked]
      rw [dispatch_shape, evaluateHOLFiniteState_ite, testHalted]
      simpa only [if_neg (show (1#64 : BitVec 64) ≠ 0 from by decide), ite_self, markDone] using assigned
    exact body_after_head source headRun
  | exhausted active pc length markedMapped markedStored activeMapped activeStored activeNonzero pcMapped pcStored lengthMapped lengthStored finished =>
    let declared := bind source "done" 0#64
    let pcState := bind declared "pc" pc
    have readMarked := Input.global_field_read declared "cur_cont" cont 32#64 0#64 continuation markedMapped markedStored
    change eval declared (RootExit.recordLoad 32#64) = some (.val (.word 0#64)) at readMarked
    have testMarked : eval declared markedCondition = some (.val (.word 0#64)) := by
      simp only [eval] at readMarked
      simp [eval, markedCondition, evalHOLExact, readMarked, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have readActive := frame_read declared frame 104#64 active ev activeMapped activeStored
    have testActive : eval declared haltedCondition = some (.val (.word 0#64)) := by
      simp only [eval] at readActive
      simp [eval, haltedCondition, evalHOLExact, readActive, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, activeNonzero]
    have readPc := frame_read declared frame 0#64 pc ev pcMapped pcStored
    have readLength := frame_read pcState frame 56#64 length ev lengthMapped lengthStored
    have pcLocal : pcState.locals.lookup (ofString "pc") = some (.val (.word pc)) := bind_lookup_same _ _ _
    have notLower : ¬pc < length := by change ¬pc.toNat < length.toNat; omega
    have testEnd : eval pcState codeEndCondition = some (.val (.word 1#64)) := by
      simp only [eval] at readLength
      simp [eval, codeEndCondition, evalHOLExact, localVar, toExact, pcLocal, readLength, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, notLower]
    have doneLocal : pcState.locals.lookup (ofString "done") = some (.val (.word 0#64)) :=
      (bind_lookup_other declared "pc" "done" pc (by decide)).trans (bind_lookup_same _ _ _)
    have assigned := StateSteps.assign_execute pcState "done" (.const 1#64) 0#64 1#64 doneLocal rfl
    have branchRun : evaluateHOLFiniteState pcState (.ite codeEndCondition markDone opcodeBranch) = (none, bind pcState "done" 1#64) := by
      simp only [eval] at testEnd
      rw [evaluateHOLFiniteState_ite, testEnd]
      change (if (1#64 : BitVec 64) = 0 then evaluateHOLFiniteState pcState opcodeBranch else evaluateHOLFiniteState pcState markDone) = _
      rw [if_neg (show (1#64 : BitVec 64) ≠ 0 from by decide)]
      exact assigned
    have pcRun : evaluateHOLFiniteState declared pcBranch = (none, markedState source) := by
      rw [pc_shape]
      have run := Input.ScalarScope.declare_execute declared (bind pcState "done" 1#64) "pc" (frameLoad 0#64) pc _ none readPc branchRun
      rw [restore_bind_other declared pcState "pc" "done" 1#64 (by decide)] at run
      dsimp only [pcState] at run
      rw [restore_bound] at run
      exact run
    have headRun : evaluateHOLFiniteState declared head = (none, markedState source) := by
      simp only [eval] at testMarked testActive
      rw [head_shape, evaluateHOLFiniteState_ite, testMarked]
      change (if (0#64 : BitVec 64) = 0 then evaluateHOLFiniteState declared dispatchBranch else evaluateHOLFiniteState declared markDone) = _
      rw [if_pos (show (0#64 : BitVec 64) = 0 from by decide), dispatch_shape, evaluateHOLFiniteState_ite, testActive]
      change (if (0#64 : BitVec 64) = 0 then evaluateHOLFiniteState declared pcBranch else evaluateHOLFiniteState declared markDone) = _
      rw [if_pos (show (0#64 : BitVec 64) = 0 from by decide)]
      exact pcRun
    exact body_after_head source headRun

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.ImmediateDone.of_fields
#print axioms InitECandidate.Solver.GasBudget.RunFrames.done_body_execute
