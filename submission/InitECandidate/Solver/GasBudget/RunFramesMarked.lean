import InitECandidate.Solver.GasBudget.RunFramesProgram

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

def markedState (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind (bind source "done" 0#64) "done" 1#64

theorem body_after_head (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (headRun : evaluateHOLFiniteState (bind source "done" 0#64) head = (none, markedState source)) :
    evaluateHOLFiniteState source loopBody =
      (let output := evaluateHOLFiniteState (markedState source) RootExit.selected
       (output.1, restore source "done" output.2)) := by
  let declared := bind source "done" 0#64
  let marked := markedState source
  have doneLocal : marked.locals.lookup (ofString "done") = some (.val (.word 1#64)) := bind_lookup_same _ _ _
  have doneTest : eval marked doneCondition = some (.val (.word 1#64)) := by
    simp [eval, doneCondition, evalHOLExact, localVar, toExact, doneLocal, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have branchRun : evaluateHOLFiniteState marked (.ite doneCondition RootExit.selected .skip) = evaluateHOLFiniteState marked RootExit.selected := by
    simp only [eval] at doneTest
    rw [evaluateHOLFiniteState_ite, doneTest]
    simp
  have seqRun : evaluateHOLFiniteState declared (.seq head (.ite doneCondition RootExit.selected .skip)) = evaluateHOLFiniteState marked RootExit.selected := by
    rw [StateSteps.next_sequence declared marked _ _ headRun (Nat.le_refl _), branchRun]
  have allRun := Input.ScalarScope.declare_execute source (evaluateHOLFiniteState marked RootExit.selected).2 "done" (.const 0#64) 0#64
    (.seq head (.ite doneCondition RootExit.selected .skip)) (evaluateHOLFiniteState marked RootExit.selected).1 rfl seqRun
  rw [loop_body_shape]
  exact allRun


/-- An already-marked continuation selects the actual completion branch in
the full loop body. Its done declaration/assignment and lexical restoration
are exact, including any result from the real epilogue/exit continuation. -/
theorem marked_body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cont flag : BitVec 64)
    (continuation : source.globals.lookup (ofString "cur_cont") = some (.val (.word cont)))
    (mapped : source.memaddrs (cont + 32#64)) (stored : source.memory (cont + 32#64) = .word flag) (nonzero : flag ≠ 0#64) :
    evaluateHOLFiniteState source loopBody =
      (let output := evaluateHOLFiniteState (markedState source) RootExit.selected
       (output.1, restore source "done" output.2)) := by
  let declared := bind source "done" 0#64
  let marked := markedState source
  have read := Input.global_field_read declared "cur_cont" cont 32#64 flag continuation mapped stored
  change eval declared (RootExit.recordLoad 32#64) = some (.val (.word flag)) at read
  have test : eval declared markedCondition = some (.val (.word 1#64)) := by
    simp only [eval] at read
    simp [eval, markedCondition, evalHOLExact, read, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, nonzero]
  have assignRun : evaluateHOLFiniteState declared markDone = (none, marked) :=
    StateSteps.assign_execute declared "done" (.const 1#64) 0#64 1#64 (bind_lookup_same _ _ _) rfl
  have headRun : evaluateHOLFiniteState declared head = (none, marked) := by
    simp only [eval] at test
    rw [head_shape, evaluateHOLFiniteState_ite, test]
    simpa using assignRun
  exact body_after_head source headRun

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.marked_body_execute

#print axioms InitECandidate.Solver.GasBudget.RunFrames.body_after_head
