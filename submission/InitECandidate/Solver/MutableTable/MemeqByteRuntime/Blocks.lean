import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Tail

namespace InitECandidate.Solver.MutableTable.MemeqByteRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix

def price (remaining : Nat) : Nat := remaining / 8 + remaining % 8
def program : ProgHOL 64 := .seq (.while condition8 blockBody) tailProgram

theorem price_step (remaining : Nat) (large : 8 ≤ remaining) : price remaining = price (remaining - 8) + 1 := by
  unfold price
  omega

theorem price_small (remaining : Nat) (small : remaining < 8) : price remaining = remaining := by
  unfold price
  omega

set_option maxRecDepth 4000 in
/-- Both actual unaligned comparison loops and final return, for all small
key lengths. Each eight-byte block consumes one source clock and each final
byte consumes one. Every early mismatch and complete pure state frame is
included; this does not price the straight-line byte tests themselves. -/
theorem blocks_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (a b : BitVec 64) (length index : Nat)
    (left right : Nat → UInt8) (inputs : Inputs source a b length left right)
    (current : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index))))
    (small : length ≤ 64) (inside : index ≤ length) (enough : price (length - index) ≤ source.clock) :
    ∃ (spent : Nat) (answer : BitVec 64), spent ≤ price (length - index) ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState source program =
        (some (.returned (.val (.word answer))), emptyLocalsHOLFinite {source with clock := source.clock - spent}) := by
  generalize rankEq : length - index = rank
  induction rank using Nat.strongRecOn generalizing source index with
  | ind rank ih =>
    rw [rankEq] at enough
    have test := condition8_read source index length small inside current inputs.lengthLocal
    by_cases active : index + 8 ≤ length
    · have entering : eval source condition8 = some (.val (.word 1#64)) := by simpa only [if_pos active] using test
      have priceStep : price (length - index) = price (length - (index + 8)) + 1 := by
        have decrement : length - (index + 8) = (length - index) - 8 := by omega
        rw [decrement]
        exact price_step _ (by omega)
      rw [rankEq] at priceStep
      have positive : source.clock ≠ 0 := by omega
      let entry := decClockHOLFinite source
      have entryInputs : Inputs entry a b length left right :=
        ⟨inputs.aLocal, inputs.bLocal, inputs.lengthLocal, inputs.leftRead, inputs.rightRead⟩
      have bodyRun := block_execute entry a b length index left right entryInputs current active
      by_cases agrees : CompareChain.agrees (Memeq32.byteChecks (blockWords left index) (blockWords right index)) = true
      · rw [if_pos agrees] at bodyRun
        let next := Memeq32.indexed source (source.clock - 1) (index + 8)
        have addition : BitVec.ofNat 64 index + 8#64 = BitVec.ofNat 64 (index + 8) := by rw [BitVec.ofNat_add]
        have nextEq : WitnessRadix.QueryBranch.bind entry "i" (BitVec.ofNat 64 index + 8#64) = next := by rw [addition]; rfl
        rw [nextEq] at bodyRun
        have smaller : length - (index + 8) < rank := by omega
        obtain ⟨paid, answer, paidBound, answerBound, tailRun⟩ := ih (length - (index + 8)) smaller next (index + 8)
          (inputs.indexed (source.clock - 1) (index + 8)) (Memeq32.indexed_current source _ _) active
          (by change price (length - (index + 8)) ≤ source.clock - 1; omega) rfl
        have clocks : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
        have finalShape : emptyLocalsHOLFinite {next with clock := next.clock - paid} =
            emptyLocalsHOLFinite {source with clock := source.clock - (paid + 1)} := by
          change emptyLocalsHOLFinite {source with clock := source.clock - 1 - paid} = _
          rw [clocks]
        have step := loop_continue source next condition8 blockBody tailProgram entering positive bodyRun (Nat.le_refl _)
        change evaluateHOLFiniteState source program = evaluateHOLFiniteState next program at step
        rw [tailRun, finalShape] at step
        exact ⟨paid + 1, answer, by omega, answerBound, step⟩
      · have differs : CompareChain.agrees (Memeq32.byteChecks (blockWords left index) (blockWords right index)) = false := Bool.eq_false_iff.mpr agrees
        simp only [differs, Bool.false_eq_true, ↓reduceIte] at bodyRun
        have step := loop_return source (emptyLocalsHOLFinite entry) condition8 blockBody tailProgram 0#64
          entering positive bodyRun (Nat.le_refl _)
        exact ⟨1, 0#64, by omega, Or.inl rfl, step⟩
    · have stopped : eval source condition8 = some (.val (.word 0#64)) := by simpa only [if_neg active] using test
      have cost : price (length - index) = length - index := price_small _ (by omega)
      rw [rankEq] at cost
      obtain ⟨paid, answer, paidBound, answerBound, tailRun⟩ := tail_execute source a b length index left right inputs current small inside
        (by rw [rankEq, ← cost]; exact enough)
      refine ⟨paid, answer, by omega, answerBound, ?_⟩
      rw [program, loop_stop source condition8 blockBody tailProgram stopped]
      exact tailRun

end InitECandidate.Solver.MutableTable.MemeqByteRuntime

#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.price_step
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.price_small
#print axioms InitECandidate.Solver.MutableTable.MemeqByteRuntime.blocks_execute
