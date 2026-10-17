import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Control

namespace InitECandidate.Solver.MutableTable.MemeqByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

def tailProgram : ProgHOL 64 := .seq (.while condition1 byteBody) (CompareChain.returned 1#64)

set_option maxRecDepth 4000 in
/-- Entire real trailing-byte loop plus success return. Every mismatch is
included; it uses at most the remaining byte count in source clocks and has
no memory/FFI effect. Fixed key sizes need at most four such byte steps. -/
theorem tail_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (a b : BitVec 64) (length index : Nat)
    (left right : Nat → UInt8) (inputs : Inputs source a b length left right)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (small : length ≤ 64) (inside : index ≤ length) (enough : length - index ≤ source.clock) :
    ∃ (spent : Nat) (answer : BitVec 64), spent ≤ length - index ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState source tailProgram =
        (some (.returned (.val (.word answer))), emptyLocalsHOLFinite {source with clock := source.clock - spent}) := by
  generalize rankEq : length - index = rank
  induction rank using Nat.strongRecOn generalizing source index with
  | ind rank ih =>
    have test := condition1_read source index length small inside current inputs.lengthLocal
    by_cases active : index < length
    · have entering : eval source condition1 = some (.val (.word 1#64)) := by simpa only [if_pos active] using test
      have positive : source.clock ≠ 0 := by omega
      let entry := decClockHOLFinite source
      have entryInputs : Inputs entry a b length left right :=
        ⟨inputs.aLocal, inputs.bLocal, inputs.lengthLocal, inputs.leftRead, inputs.rightRead⟩
      have bodyRun := byte_execute entry a b length index left right entryInputs current active
      by_cases agrees : CompareChain.agrees (byteChecks (left index) (right index)) = true
      · rw [if_pos agrees] at bodyRun
        let next := Memeq32.indexed source (source.clock - 1) (index + 1)
        have addition : BitVec.ofNat 64 index + 1#64 = BitVec.ofNat 64 (index + 1) := by rw [BitVec.ofNat_add]
        have nextEq : WitnessRadix.QueryBranch.bind entry "i" (BitVec.ofNat 64 index + 1#64) = next := by rw [addition]; rfl
        rw [nextEq] at bodyRun
        have smaller : length - (index + 1) < rank := by omega
        obtain ⟨paid, answer, paidBound, answerBound, tailRun⟩ := ih (length - (index + 1)) smaller next (index + 1)
          (inputs.indexed (source.clock - 1) (index + 1)) (Memeq32.indexed_current source _ _) (by omega)
          (by change length - (index + 1) ≤ source.clock - 1; omega) rfl
        have clocks : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
        have finalShape : emptyLocalsHOLFinite {next with clock := next.clock - paid} =
            emptyLocalsHOLFinite {source with clock := source.clock - (paid + 1)} := by
          change emptyLocalsHOLFinite {source with clock := source.clock - 1 - paid} = _
          rw [clocks]
        have step := loop_continue source next condition1 byteBody (CompareChain.returned 1#64) entering positive bodyRun (Nat.le_refl _)
        change evaluateHOLFiniteState source tailProgram = evaluateHOLFiniteState next tailProgram at step
        rw [tailRun, finalShape] at step
        exact ⟨paid + 1, answer, by omega, answerBound, step⟩
      · have differs : CompareChain.agrees (byteChecks (left index) (right index)) = false := Bool.eq_false_iff.mpr agrees
        simp only [differs, Bool.false_eq_true, ↓reduceIte] at bodyRun
        have step := loop_return source (emptyLocalsHOLFinite entry) condition1 byteBody (CompareChain.returned 1#64) 0#64
          entering positive bodyRun (Nat.le_refl _)
        exact ⟨1, 0#64, by omega, Or.inl rfl, step⟩
    · have stopped : eval source condition1 = some (.val (.word 0#64)) := by simpa only [if_neg active] using test
      refine ⟨0, 1#64, by omega, Or.inr rfl, ?_⟩
      rw [tailProgram, loop_stop source condition1 byteBody (CompareChain.returned 1#64) stopped]
      simpa only [Nat.sub_zero] using CompareChain.return_word source 1#64

end InitECandidate.Solver.MutableTable.MemeqByteRuntime

#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.tail_execute
