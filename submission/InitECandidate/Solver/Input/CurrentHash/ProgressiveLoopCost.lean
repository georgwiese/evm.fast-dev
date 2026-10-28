import InitECandidate.Solver.Input.CurrentHash.ProgressiveStepCost
import InitECandidate.Solver.Input.ClockCostTerminatingLoop
import InitECandidate.Solver.Input.LoopInvariantNoControl

namespace InitECandidate.Solver.Input.CurrentHash.ProgressiveLoopCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open Progressive ProgressiveRound

theorem offset_bound (k : Nat) (bounded : k ≤ 15) : offset k ≤ 357913941 := by
  have upper := offset_mono bounded
  have number : offset 15 = 357913941 := by decide
  rw [number] at upper
  exact upper

def invariant (p roots : BitVec 64) (n : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ k : Nat, k ≤ 15 ∧ Round source p roots n k

def credit (n : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  currentAllowance n (CounterFlow.counterWord source (ofString "off")).toNat (CounterFlow.counterWord source (ofString "k")).toNat

theorem credit_eq (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n k : Nat)
    (data : Round source p roots n k) (bounded : k ≤ 15) : credit n source = currentAllowance n (offset k) k := by
  have offBound := offset_bound k bounded
  have offNumber : (BitVec.ofNat 64 (offset k)).toNat = offset k := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have kNumber : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp [credit, CounterFlow.counterWord, data.position, data.round, valueWord, offNumber, kNumber]

theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n k : Nat)
    (data : Round source p roots n k) (bounded : n ≤ 134217728) (round : k ≤ 15) :
    evalHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) test =
      some (.val (.word (if offset k < n then 1#64 else 0#64))) := by
  have offBound := offset_bound k round
  have offNumber : (BitVec.ofNat 64 (offset k)).toNat = offset k := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have nNumber : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp [evalHOLFinite, evalHOLExact, toExact, test, localVar, data.position, data.count,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def, offNumber, nNumber]

/-- Each real geometric round pays for its actual capped chunks plus200ticks.
The actual continuation increases k and removes those chunks from the remaining
allowance. At most15rounds are derived from the current count ceiling. -/
theorem cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n k : Nat)
    (bounded : n ≤ 134217728) (round : k ≤ 15) (data : Round source p roots n k)
    (installed : OriginalCode.Installed source.code) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source loop = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ currentAllowance n (offset k) k := by
  have transition : ∀ state : PanSemStateFiniteExact 64 Guest.HostMemory, state.code = source.code → invariant p roots n state → ∀ word,
      evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) test = some (.val (.word word)) → word ≠ 0 → state.clock ≠ 0 →
      let output := evaluateHOLFiniteState (decClockHOLFinite state) step
      output.1 ≠ some .timeOut → state.clock - output.2.clock ≤ credit n state ∧
      ((output.1 = none ∨ output.1 = some .continue) → invariant p roots n output.2 ∧
        state.clock - output.2.clock + credit n output.2 ≤ credit n state) := by
    intro state codeEq valid word read nonzero funded
    dsimp only
    intro bodyNotTimeout
    obtain ⟨position, positionBound, current⟩ := valid
    have expected := test_read state p roots n position current bounded positionBound
    have active : offset position < n := by
      by_cases active : offset position < n
      · exact active
      rw [if_neg active] at expected
      have zero : word = 0#64 := by simpa only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using read.symm.trans expected
      exact False.elim (nonzero zero)
    have currentRound := active_round n position bounded active
    have positive : 0 < 4^position := Nat.pow_pos (by decide)
    have amortized := current_amortized_round n (offset position) (4^position) position active positive currentRound
    have overhead := current_round_price position currentRound
    let output := evaluateHOLFiniteState (decClockHOLFinite state) step
    have currentCode : OriginalCode.Installed (decClockHOLFinite state).code := by change OriginalCode.Installed state.code; rw [codeEq]; exact installed
    have bodyPrice := ProgressiveStepCost.cost (decClockHOLFinite state) output.2 p roots n position bounded active current.dec_clock currentCode output.1 rfl bodyNotTimeout
    have bodyClock := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) step
    change state.clock - 1 - output.2.clock ≤ 88*min (4^position) (n-offset position) + 4*(2*position) + 49 at bodyPrice
    change output.2.clock ≤ state.clock - 1 at bodyClock
    have spent : state.clock - output.2.clock ≤ 88*min (4^position) (n-offset position) + 200 := by omega
    have currentCredit := credit_eq state p roots n position current positionBound
    have stopped : state.clock - output.2.clock ≤ credit n state := by rw [currentCredit]; omega
    refine ⟨stopped, ?_⟩
    intro continuing
    have summary := (step_other (ofString "n") (by decide) (by decide) (by decide) (by decide)).summary_full (decClockHOLFinite state)
    unfold LocalSummary at summary
    have normal : output.1 = none := continuing.resolve_right summary.2.2.2
    have continued : evaluateHOLFiniteState (decClockHOLFinite state) step = (none, output.2) := Prod.ext normal rfl
    have next := ProgressiveRound.step_normal (decClockHOLFinite state) output.2 p roots n position bounded active current.dec_clock continued
    have nextBound : position + 1 ≤ 15 := by omega
    have nextCredit := credit_eq output.2 p roots n (position+1) next nextBound
    have paid : state.clock - output.2.clock + credit n output.2 ≤ credit n state := by
      rw [nextCredit, currentCredit, offset]
      omega
    exact ⟨⟨position+1, nextBound, next⟩, paid⟩
  rw [loop_shape.1] at actual
  have priced := ClockCost.potential_loop_terminating source.code test step (invariant p roots n) (credit n) transition source rfl ⟨k, round, data⟩
    (by rw [actual]; exact notTimeout)
  rw [actual] at priced
  rw [credit_eq source p roots n k data round] at priced
  exact priced

/-- The same actual normal loop establishes its terminal geometric state;
this supplies the real final fold count instead of assuming one. -/
theorem normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots : BitVec 64) (n k : Nat)
    (bounded : n ≤ 134217728) (round : k ≤ 15) (data : Round source p roots n k)
    (actual : evaluateHOLFiniteState source loop = (none, post)) : invariant p roots n post := by
  rw [loop_shape.1] at actual
  apply loop_invariant_no_control source.code test step
    (fun current => ((step_other (ofString "n") (by decide) (by decide) (by decide) (by decide)).summary_full current).2.2)
    (invariant p roots n) _ source post rfl ⟨k, round, data⟩ actual
  intro current codeEq ready word read nonzero funded target continued
  obtain ⟨position, positionBound, data⟩ := ready
  have expected := test_read current p roots n position data bounded positionBound
  have active : offset position < n := by
    by_cases active : offset position < n
    · exact active
    rw [if_neg active] at expected
    have zero : word = 0#64 := by simpa only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using read.symm.trans expected
    exact False.elim (nonzero zero)
  have nextBound := active_round n position bounded active
  exact ⟨position+1, by omega, ProgressiveRound.step_normal (decClockHOLFinite current) target p roots n position bounded active data.dec_clock continued⟩

end InitECandidate.Solver.Input.CurrentHash.ProgressiveLoopCost

#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveLoopCost.offset_bound
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveLoopCost.credit_eq
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveLoopCost.test_read
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveLoopCost.cost

#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveLoopCost.normal
