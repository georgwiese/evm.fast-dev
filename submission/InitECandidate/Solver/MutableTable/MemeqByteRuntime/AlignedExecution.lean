import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Aligned32Blocks
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Execution
import InitECandidate.Solver.MutableTable.MemeqSizedFast

namespace InitECandidate.Solver.MutableTable.MemeqByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

theorem skip_size_continuation {F : Type} (source : PanSemStateFiniteExact 64 F) (length size : Nat)
    (branch tail : ProgHOL 64)
    (len : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 length))))
    (small : length ≤ 64) (sizeSmall : size ≤ 64) (different : length ≠ size) :
    evaluateHOLFiniteState source (.seq (.ite (Memeq32.sizeTest (BitVec.ofNat 64 size)) branch .skip) tail) =
      evaluateHOLFiniteState source tail := by
  have unequal : BitVec.ofNat 64 length ≠ BitVec.ofNat 64 size := by
    intro same
    have numeric := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat] at numeric
    omega
  have skipped : evaluateHOLFiniteState source (.ite (Memeq32.sizeTest (BitVec.ofNat 64 size)) branch .skip) = (none, source) := by
    simp [Memeq32.sizeTest, evaluateHOLFiniteState_ite, localVar, evalHOLExact, toExact, len,
      unequal, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  exact StateSteps.next_sequence source source _ tail skipped (Nat.le_refl _)

/-- Whole original aligned comparison fallback, including its32-byte and
8-byte word loops followed by the actual byte fallback, final return and
outer declaration scope. Applies to28/60-byte indexed keys. -/
theorem aligned_other_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64) (length : Nat)
    (left right : Nat → UInt8) (leftWords rightWords : Nat → BitVec 64)
    (inputs : WordInputs source a b length left right leftWords rightWords)
    (small : length ≤ 64) (not20 : length ≠ 20) (not32 : length ≠ 32) (not52 : length ≠ 52)
    (aligned : (a ||| b) &&& 7#64 = 0#64) (enough : price length ≤ source.clock) :
    ∃ (spent : Nat) (answer : BitVec 64), spent ≤ price length ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState source Memeq32.body = (some (.returned (.val (.word answer))),
        restore source "i" (emptyLocalsHOLFinite {source with clock := source.clock - spent})) := by
  let initial := Memeq32.indexed source source.clock 0
  have initialInputs : WordInputs initial a b length left right leftWords rightWords := inputs.indexed source.clock 0
  obtain ⟨spent, answer, spentBound, answerBound, run⟩ := aligned32_blocks_execute initial a b length 0 left right leftWords rightWords initialInputs
    (Memeq32.indexed_current source _ _) small (by omega) (by decide)
    (by change price (length - 0) ≤ source.clock; simpa only [Nat.sub_zero] using enough)
  have finalShape : emptyLocalsHOLFinite {initial with clock := initial.clock - spent} =
      emptyLocalsHOLFinite {source with clock := source.clock - spent} := rfl
  rw [finalShape] at run
  have branchRun : evaluateHOLFiniteState initial (.seq MemeqSized.alignedProgram program) =
      (some (.returned (.val (.word answer))), emptyLocalsHOLFinite {source with clock := source.clock - spent}) := by
    rw [MemeqSized.alignedProgram, sequence_assoc,
      skip_size_continuation initial length 20 _ _ initialInputs.bytes.lengthLocal small (by decide) not20,
      sequence_assoc,
      skip_size_continuation initial length 32 _ _ initialInputs.bytes.lengthLocal small (by decide) not32,
      MemeqSized.other_shape, sequence_assoc,
      skip_size_continuation initial length 52 _ _ initialInputs.bytes.lengthLocal small (by decide) not52,
      aligned_loops_shape, sequence_assoc]
    exact run
  have alignmentRead : eval initial Memeq32.alignmentTest = some (.val (.word 1#64)) := by
    simp [eval, Memeq32.alignmentTest, localVar, evalHOLExact, evalListHOLExact, toExact,
      initialInputs.bytes.aLocal, initialInputs.bytes.bLocal, valueIsWord, valueWord, wordOpHOL, wordOp,
      OrOp.or, AndOp.and, aligned, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have select : evaluateHOLFiniteState initial (.ite Memeq32.alignmentTest MemeqSized.alignedProgram .skip) =
      evaluateHOLFiniteState initial MemeqSized.alignedProgram := by
    simp only [eval] at alignmentRead
    rw [evaluateHOLFiniteState_ite, alignmentRead]
    simp
  have full : evaluateHOLFiniteState initial (.seq (.ite Memeq32.alignmentTest MemeqSized.alignedProgram .skip) program) =
      (some (.returned (.val (.word answer))), emptyLocalsHOLFinite {source with clock := source.clock - spent}) := by
    rw [evaluateHOLFiniteState_seq_line780, select, ← evaluateHOLFiniteState_seq_line780]
    exact branchRun
  refine ⟨spent, answer, by simpa only [Nat.sub_zero] using spentBound, answerBound, ?_⟩
  rw [Memeq32.body_shape]
  have actual := Input.ScalarScope.declare_execute source _ "i" (.const 0#64) 0#64 _ _ rfl full
  simpa only [actual_tail, MemeqSized.alignedProgram] using actual

end InitECandidate.Solver.MutableTable.MemeqByteRuntime

#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.skip_size_continuation
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.aligned_other_execute
