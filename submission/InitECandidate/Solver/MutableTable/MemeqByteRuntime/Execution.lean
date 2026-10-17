import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Blocks
import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.MutableTable.MemeqByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

theorem actual_tail : Memeq32.parts.tailCode = program := by
  exact Memeq32.tail_shape

/-- Whole original memeq through its real unaligned byte fallback. Any key
length at most64 is permitted, including20/32/52/60; no helper execution is an
assumption. The actual return is0or1 and all canonical fields remain pure. -/
theorem unaligned_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (a b : BitVec 64) (length : Nat)
    (left right : Nat → UInt8) (inputs : Inputs source a b length left right)
    (small : length ≤ 64) (unaligned : (a ||| b) &&& 7#64 ≠ 0#64) (enough : price length ≤ source.clock) :
    ∃ (spent : Nat) (answer : BitVec 64), spent ≤ price length ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState source Memeq32.body = (some (.returned (.val (.word answer))),
        restore source "i" (emptyLocalsHOLFinite {source with clock := source.clock - spent})) := by
  let initial := Memeq32.indexed source source.clock 0
  have initialInputs : Inputs initial a b length left right := inputs.indexed source.clock 0
  obtain ⟨spent, answer, spentBound, answerBound, tailRun⟩ := blocks_execute initial a b length 0 left right initialInputs
    (Memeq32.indexed_current source _ _) small (by omega) (by change price (length - 0) ≤ source.clock; simpa only [Nat.sub_zero] using enough)
  have tailShape : emptyLocalsHOLFinite {initial with clock := initial.clock - spent} =
      emptyLocalsHOLFinite {source with clock := source.clock - spent} := rfl
  rw [tailShape, ← actual_tail] at tailRun
  have alignmentRead : eval initial Memeq32.alignmentTest = some (.val (.word 0#64)) := by
    simp [eval, Memeq32.alignmentTest, localVar, evalHOLExact, evalListHOLExact, toExact,
      initialInputs.aLocal, initialInputs.bLocal, valueIsWord, valueWord, wordOpHOL, wordOp,
      OrOp.or, AndOp.and, unaligned, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  let front := ProgHOL.ite Memeq32.alignmentTest
    (.seq (.ite (Memeq32.sizeTest 20#64) Memeq32.parts.twenty .skip)
      (.seq (.ite (Memeq32.sizeTest 32#64) Memeq32.parts.thirtyTwo .skip) Memeq32.parts.otherAligned)) .skip
  have skipped : evaluateHOLFiniteState initial front = (none, initial) := by
    simp only [eval] at alignmentRead
    dsimp only [front]
    rw [evaluateHOLFiniteState_ite]
    simp [alignmentRead, evaluateHOLFiniteState_skip]
  have suffix := StateSteps.next_sequence initial initial front Memeq32.parts.tailCode skipped (Nat.le_refl _)
  rw [tailRun] at suffix
  refine ⟨spent, answer, by simpa only [Nat.sub_zero] using spentBound, answerBound, ?_⟩
  rw [Memeq32.body_shape]
  exact Input.ScalarScope.declare_execute source _ "i" (.const 0#64) 0#64 _ _ rfl suffix

end InitECandidate.Solver.MutableTable.MemeqByteRuntime

#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.actual_tail
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.unaligned_execute
