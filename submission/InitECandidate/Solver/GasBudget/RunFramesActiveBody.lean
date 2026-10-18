import InitECandidate.Solver.GasBudget.RunFramesActiveHead
import InitECandidate.Solver.Input.NoneControl

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def activeEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pc : BitVec 64) :=
  bind (bind source "done" 0#64) "pc" pc

private theorem restore_other (saved source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name key : String) (different : ofString key ≠ ofString name) :
    (restore saved name source).locals.lookup (ofString key) = source.locals.lookup (ofString key) := by
  change (HolFiniteMapExact.resVarEq source.locals (ofString name, saved.locals.lookup (ofString name))).lookup (ofString key) = _
  rw [lookup_resVarEq_toExact]
  cases saved.locals.lookup (ofString name) <;> simp [resVarHOLExact, different]

/-- An actual normal active iteration ran the genuine opcode branch and
skipped the epilogue/child-completion tail. Even a caught opcode error leaves
the current local done0; its marked continuation is read next iteration. -/
theorem active_body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame cont running pc length : BitVec 64)
    (header : ActiveHeader source frame cont running pc length)
    (normal : evaluateHOLFiniteState source loopBody = (none, post)) :
    ∃ inner, evaluateHOLFiniteState (activeEntry source pc) opcodeBranch = (none, inner) ∧
      post = restore source "done" (restore (bind source "done" 0#64) "pc" inner) ∧
      post.clock = inner.clock ∧ post.memory = inner.memory := by
  rw [loop_body_shape] at normal
  let declared := bind source "done" 0#64
  obtain ⟨after, sequenceRun, postEq⟩ := Input.declaration_none source post "done" (.const 0#64) 0#64
    (.seq head (.ite doneCondition RootExit.selected .skip)) rfl normal
  obtain ⟨headed, headRun, tailRun⟩ := Input.sequence_none declared after head (.ite doneCondition RootExit.selected .skip) sequenceRun
  rw [active_head_execute declared frame cont running pc length header] at headRun
  let inner := (evaluateHOLFiniteState (activeEntry source pc) opcodeBranch).2
  have resultEq := congrArg Prod.fst headRun
  have opcodeRun : evaluateHOLFiniteState (activeEntry source pc) opcodeBranch = (none, inner) := Prod.ext resultEq rfl
  have headedEq := congrArg Prod.snd headRun
  change restore declared "pc" inner = headed at headedEq
  have initialDone : (activeEntry source pc).locals.lookup (ofString "done") = some (.val (.word 0#64)) :=
    (bind_lookup_other declared "pc" "done" pc (by decide)).trans (bind_lookup_same source "done" 0#64)
  have innerDone := (opcode_done_normal (activeEntry source pc) inner opcodeRun).trans initialDone
  have headedDone : headed.locals.lookup (ofString "done") = some (.val (.word 0#64)) := by
    rw [← headedEq]
    exact (restore_other declared inner "pc" "done" (by decide)).trans innerDone
  have doneTest : eval headed doneCondition = some (.val (.word 0#64)) := by
    simp [eval, doneCondition, localVar, evalHOLExact, toExact, headedDone, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have skipRun : evaluateHOLFiniteState headed (.ite doneCondition RootExit.selected .skip) = (none, headed) := by
    simp only [eval] at doneTest
    rw [evaluateHOLFiniteState_ite, doneTest]
    exact evaluateHOLFiniteState_skip headed
  rw [skipRun] at tailRun
  have afterEq := congrArg Prod.snd tailRun
  change headed = after at afterEq
  rw [← afterEq, ← headedEq] at postEq
  exact ⟨inner, opcodeRun, postEq, by rw [postEq]; rfl, by rw [postEq]; rfl⟩

/-- The whole real active loop body exposes actual original dispatch or its
actual caught handler, with a genuinely read byte and lexical scopes. -/
theorem active_body_dispatch_cases (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame cont running pc length : BitVec 64)
    (header : ActiveHeader source frame cont running pc length)
    (installed : Input.OriginalCode.Installed source.code) (shapes : Input.OriginalExceptions.Installed source.eshapes)
    (normal : evaluateHOLFiniteState source loopBody = (none, post)) :
    ∃ inner handled,
      CaughtDispatchCases (bind (activeEntry source pc) "err" 0#64) handled ∧
      inner = restore (activeEntry source pc) "err" handled ∧
      post = restore source "done" (restore (bind source "done" 0#64) "pc" inner) ∧
      post.clock = handled.clock ∧ post.memory = handled.memory := by
  obtain ⟨inner, opcodeRun, postEq, clock, memory⟩ := active_body_normal source post frame cont running pc length header normal
  obtain ⟨handled, cases, innerEq⟩ := opcode_branch_cases (activeEntry source pc) inner installed shapes opcodeRun
  refine ⟨inner, handled, cases, innerEq, postEq, ?_, ?_⟩
  · rw [clock, innerEq]
    rfl
  · rw [memory, innerEq]
    rfl

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.active_body_normal
#print axioms InitECandidate.Solver.GasBudget.RunFrames.active_body_dispatch_cases
