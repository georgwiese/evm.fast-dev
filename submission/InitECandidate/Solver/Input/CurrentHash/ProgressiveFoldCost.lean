import InitECandidate.Solver.Input.ProgressiveFoldProgram
import InitECandidate.Solver.Input.CurrentHash.FixedMemoryCost
import InitECandidate.Solver.Input.CurrentHash.AllocatorCost
import InitECandidate.Solver.Input.ClockCostLoop
import InitECandidate.Solver.Input.CounterLoopCost
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.IgnoredCallLookup

namespace InitECandidate.Solver.Input.CurrentHash.ProgressiveFoldCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open Progressive

theorem step_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code foldStep 1 := by
  rw [fold_shape.2.1]
  exact ClockCost.sequence code _ _ 0 1 (ClockCost.assign code _ _) (Sha256Pair.call_cost code installed (some none) _)

def invariant (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ k : Nat, k ≤ 15 ∧ source.locals.lookup (ofString "k") = some (.val (.word (BitVec.ofNat 64 k)))
def rank (source : PanSemStateFiniteExact 64 Guest.HostMemory) := (CounterFlow.counterWord source (ofString "k")).toNat

theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (k : Nat) (inside : k ≤ 15)
    (round : source.locals.lookup (ofString "k") = some (.val (.word (BitVec.ofNat 64 k)))) :
    evalHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) foldTest = some (.val (.word (if k = 0 then 0#64 else 1#64))) := by
  have number : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have zero : BitVec.ofNat 64 k = 0#64 ↔ k = 0 := by
    constructor
    · intro same; have equal := congrArg BitVec.toNat same; simpa only [number, BitVec.toNat_ofNat] using equal
    · intro same; subst k; rfl
  simp [evalHOLFinite, evalHOLExact, toExact, foldTest, localVar, round, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, zero]

/-- Every actual final-fold outcome costs at most two ticks per saved root,
with its real decrement before each software SHA call. -/
theorem cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (k : Nat) (inside : k ≤ 15)
    (installed : OriginalCode.Installed source.code)
    (round : source.locals.lookup (ofString "k") = some (.val (.word (BitVec.ofNat 64 k)))) :
    source.clock - (evaluateHOLFiniteState source foldLoop).2.clock ≤ 2*k := by
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory, current.code = source.code → invariant current → ∀ word,
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) foldTest = some (.val (.word word)) → word ≠ 0 →
      0 < rank current ∧ (current.clock ≠ 0 → let output := evaluateHOLFiniteState (decClockHOLFinite current) foldStep
        (output.1 = none ∨ output.1 = some .continue) → invariant output.2 ∧ rank output.2 < rank current) := by
    intro current codeEq ready word read nonzero
    obtain ⟨position, bounded, cell⟩ := ready
    have expected := test_read current position bounded cell
    have positive : 0 < position := by
      by_cases zero : position = 0
      · rw [if_pos zero] at expected
        have same : word = 0#64 := by simpa only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using read.symm.trans expected
        exact False.elim (nonzero same)
      · omega
    have number : (BitVec.ofNat 64 position).toNat = position := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have rankEq : rank current = position := by simp [rank, CounterFlow.counterWord, cell, valueWord, number]
    refine ⟨by rw [rankEq]; exact positive, ?_⟩
    intro funded
    dsimp only
    intro continuing
    let output := evaluateHOLFiniteState (decClockHOLFinite current) foldStep
    have summary := (fold_other (ofString "n") (by decide)).summary_full (decClockHOLFinite current)
    unfold LocalSummary at summary
    have normal : output.1 = none := continuing.resolve_right summary.2.2.2
    have actual : evaluateHOLFiniteState (decClockHOLFinite current) foldStep = (none, output.2) := Prod.ext normal rfl
    have next := fold_advances (decClockHOLFinite current) output.2 position positive (by omega) cell actual
    have nextNumber : (BitVec.ofNat 64 (position-1)).toNat = position-1 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have nextRank : rank output.2 = position-1 := by simp [rank, CounterFlow.counterWord, next, valueWord, nextNumber]
    exact ⟨⟨position-1, by omega, next⟩, by rw [nextRank, rankEq]; omega⟩
  have priced := ClockCost.ranked_loop source.code foldTest foldStep 1 invariant rank (step_cost source.code installed) progress source rfl ⟨k, inside, round⟩
  have number : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [fold_shape.1]
  simpa only [rank, CounterFlow.counterWord, round, Option.getD_some, valueWord, number] using priced

theorem output_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code afterFold 43 := by
  rw [fold_shape.2.2.2.2.2]
  exact ClockCost.sequence code _ _ 42 1 (FixedMemoryCost.copy code installed (some none) _ _ 32 (by decide))
    (ClockCost.sequence code _ _ 1 0 (AllocatorCost.release_call code installed (some none) _) (ClockCost.returned code _))

theorem after_zero_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (k : Nat) (inside : k ≤ 15)
    (installed : OriginalCode.Installed source.code)
    (round : source.locals.lookup (ofString "k") = some (.val (.word (BitVec.ofNat 64 k)))) :
    source.clock - (evaluateHOLFiniteState source afterZeroAcc).2.clock ≤ 2*k+43 := by
  rw [fold_shape.2.2.2.2.1]
  exact ClockCost.sequence_current source foldLoop afterFold (2*k) 43 (cost source k inside installed round) (output_cost source.code installed)

/-- Actual accumulator clear, final fold, output copy and release, including
all failures. Only the real final k is required; all pointer values may fail. -/
theorem suffix_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (k : Nat) (inside : k ≤ 15)
    (installed : OriginalCode.Installed source.code)
    (round : source.locals.lookup (ofString "k") = some (.val (.word (BitVec.ofNat 64 k)))) :
    source.clock - (evaluateHOLFiniteState source afterLoop).2.clock ≤ 2*k+85 := by
  rw [fold_shape.2.2.2.1]
  have composed := ClockCost.sequence_reached_current source _ afterZeroAcc 42 (2*k+43)
    (FixedMemoryCost.zero source.code installed (some none) _ 32 (by decide) source rfl) (by
      intro middle zeroed
      have cell := (CallNormal.ignored_lookup source middle (ofString "k") (ofString "memzero") zeroArguments zeroed).trans round
      have currentCode : OriginalCode.Installed middle.code := by rw [(evaluation_fields source middle _ none zeroed).2.2.2]; exact installed
      exact after_zero_cost middle k inside currentCode cell)
  exact Nat.le_trans composed (by omega)

end InitECandidate.Solver.Input.CurrentHash.ProgressiveFoldCost

#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveFoldCost.step_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveFoldCost.test_read
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveFoldCost.cost
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveFoldCost.output_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveFoldCost.after_zero_cost
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveFoldCost.suffix_cost
