import InitECandidate.Solver.MutableTable.MemeqByteRuntime.AlignedBodies
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Blocks

namespace InitECandidate.Solver.MutableTable.MemeqByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

set_option maxRecDepth 4000 in
/-- Both actual aligned comparison loops and final return, for all small
key lengths. Each eight-byte block consumes one source clock and each final
byte consumes one. Every early mismatch and complete pure state frame is
included; this does not price the straight-line word/byte tests themselves. -/
theorem aligned_blocks_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (a b : BitVec 64) (length index : Nat)
    (left right : Nat → UInt8) (leftWords rightWords : Nat → BitVec 64)
    (inputs : WordInputs source a b length left right leftWords rightWords)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (small : length ≤ 64) (inside : index ≤ length) (multiple : index % 8 = 0) (enough : price (length - index) ≤ source.clock) :
    ∃ (spent : Nat) (answer : BitVec 64), spent ≤ price (length - index) ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState source alignedProgram8 =
        (some (.returned (.val (.word answer))), emptyLocalsHOLFinite {source with clock := source.clock - spent}) := by
  generalize rankEq : length - index = rank
  induction rank using Nat.strongRecOn generalizing source index with
  | ind rank ih =>
    rw [rankEq] at enough
    have test := condition8_read source index length small inside current inputs.bytes.lengthLocal
    by_cases active : index + 8 ≤ length
    · have entering : eval source condition8 = some (.val (.word 1#64)) := by simpa only [if_pos active] using test
      have priceStep : price (length - index) = price (length - (index + 8)) + 1 := by
        have decrement : length - (index + 8) = (length - index) - 8 := by omega
        rw [decrement]
        exact price_step _ (by omega)
      rw [rankEq] at priceStep
      have positive : source.clock ≠ 0 := by omega
      let entry := decClockHOLFinite source
      have entryInputs : WordInputs entry a b length left right leftWords rightWords :=
        ⟨⟨inputs.bytes.aLocal, inputs.bytes.bLocal, inputs.bytes.lengthLocal, inputs.bytes.leftRead, inputs.bytes.rightRead⟩,
         inputs.leftMapped, inputs.rightMapped, inputs.leftStored, inputs.rightStored⟩
      have bodyRun := aligned_block_execute entry a b length index left right leftWords rightWords entryInputs current active multiple
      by_cases agrees : CompareChain.agrees (wordCheck (leftWords index) (rightWords index)) = true
      · rw [if_pos agrees] at bodyRun
        let next := Memeq32.indexed source (source.clock - 1) (index + 8)
        have addition : BitVec.ofNat 64 index + 8#64 = BitVec.ofNat 64 (index + 8) := by rw [BitVec.ofNat_add]
        have nextEq : WitnessRadix.QueryBranch.bind entry "i" (BitVec.ofNat 64 index + 8#64) = next := by rw [addition]; rfl
        rw [nextEq] at bodyRun
        have smaller : length - (index + 8) < rank := by omega
        obtain ⟨paid, answer, paidBound, answerBound, tailRun⟩ := ih (length - (index + 8)) smaller next (index + 8)
          (inputs.indexed (source.clock - 1) (index + 8)) (Memeq32.indexed_current source _ _) active (by omega)
          (by change price (length - (index + 8)) ≤ source.clock - 1; omega) rfl
        have clocks : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
        have finalShape : emptyLocalsHOLFinite {next with clock := next.clock - paid} =
            emptyLocalsHOLFinite {source with clock := source.clock - (paid + 1)} := by
          change emptyLocalsHOLFinite {source with clock := source.clock - 1 - paid} = _
          rw [clocks]
        have step := loop_continue source next condition8 alignedBody program entering positive bodyRun (Nat.le_refl _)
        change evaluateHOLFiniteState source alignedProgram8 = evaluateHOLFiniteState next alignedProgram8 at step
        rw [tailRun, finalShape] at step
        exact ⟨paid + 1, answer, by omega, answerBound, step⟩
      · have differs : CompareChain.agrees (wordCheck (leftWords index) (rightWords index)) = false := Bool.eq_false_iff.mpr agrees
        simp only [differs, Bool.false_eq_true, ↓reduceIte] at bodyRun
        have step := loop_return source (emptyLocalsHOLFinite entry) condition8 alignedBody program 0#64
          entering positive bodyRun (Nat.le_refl _)
        exact ⟨1, 0#64, by omega, Or.inl rfl, step⟩
    · have stopped : eval source condition8 = some (.val (.word 0#64)) := by simpa only [if_neg active] using test
      obtain ⟨paid, answer, paidBound, answerBound, tailRun⟩ := blocks_execute source a b length index left right inputs.bytes current small inside
        (by rw [rankEq]; exact enough)
      refine ⟨paid, answer, by simpa only [rankEq] using paidBound, answerBound, ?_⟩
      rw [alignedProgram8, loop_stop source condition8 alignedBody program stopped]
      exact tailRun

end InitECandidate.Solver.MutableTable.MemeqByteRuntime

#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.aligned_blocks_execute
