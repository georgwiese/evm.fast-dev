import InitECandidate.Solver.Input.SszCurrentCode
import InitECandidate.Solver.Input.OffsetsStepProgram
import InitECandidate.Solver.Input.CounterLoopCost
import InitECandidate.Solver.Input.ClockCostCall
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.PureDecision
import InitECandidate.Solver.WitnessRadix.BindingLookup

namespace InitECandidate.Solver.Input.Offsets
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem failure_body_cost (code) : ClockCost.Bound code SszFail.body 0 := by
  rw [SszFail.body_shape]
  exact ClockCost.sequence code _ _ 0 0 (ClockCost.raised code _ _) (ClockCost.returned code _)

theorem failure_cost (code) (installed : OriginalCode.Installed code) (value : BitVec 64) :
    ClockCost.Bound code (fail value) 1 :=
  ClockCost.call_body code (some none) _ _ SszFail.formals SszFail.body .one 0
    (SszCurrentCode.fail_installed code installed) (failure_body_cost code)

theorem range_local (key : MlS) : LocalPrefix key rangeGuard :=
  .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip

theorem order_local (key : MlS) : LocalPrefix key orderGuard :=
  .ite _ (.ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip) .skip

theorem loop_local : LocalPrefix (ofString "n") loopBody := by
  rw [loop_body_shape]
  exact .dec _ _ _ (by decide) (.seq (range_local _) (.seq (order_local _) (.assign _ _ (by decide))))

theorem loop_advance : CounterFlow.Advances (ofString "i") 1 loopBody := by
  rw [loop_body_shape]
  apply CounterFlow.declared _ _ _ _ checks 1 (by decide)
  exact CounterFlow.sequence _ rangeGuard (.seq orderGuard increment) 0 1
    (CounterFlow.preserved _ _ (range_local _))
    (CounterFlow.sequence _ orderGuard increment 0 1
      (CounterFlow.preserved _ _ (order_local _)) (CounterFlow.increment _))

theorem loop_body_cost (code) (installed : OriginalCode.Installed code) :
    ClockCost.Bound code loopBody 2 := by
  have range : ClockCost.Bound code rangeGuard 1 :=
    ClockCost.conditional code _ _ _ 1 0 (failure_cost code installed _) (ClockCost.skip code)
  have order : ClockCost.Bound code orderGuard 1 :=
    ClockCost.conditional code _ _ _ 1 0
      (ClockCost.conditional code _ _ _ 1 0 (failure_cost code installed _) (ClockCost.skip code))
      (ClockCost.skip code)
  rw [loop_body_shape]
  exact ClockCost.declared code _ _ _ _ 2 (ClockCost.sequence code _ _ 1 1 range
    (ClockCost.sequence code _ _ 1 0 order (ClockCost.assign code _ _)))

def CurrentCounter (count : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ word : BitVec 64, source.locals.lookup (ofString "i") = some (.val (.word word)) ∧
    source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 count))) ∧ word.toNat ≤ count

def remaining (count : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat :=
  count - (CounterFlow.counterWord source (ofString "i")).toNat

theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : Nat) (word : BitVec 64)
    (small : count ≤ 8) (installed : OriginalCode.Installed source.code)
    (counter : source.locals.lookup (ofString "i") = some (.val (.word word)))
    (limit : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 count))))
    (bounded : word.toNat ≤ count) :
    source.clock - (evaluateHOLFiniteState source loop).2.clock ≤ 3 * (count - word.toNat) := by
  have progress : ∀ state : PanSemStateFiniteExact 64 Guest.HostMemory,
      state.code = source.code → CurrentCounter count state → ∀ observed : BitVec 64,
      evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) condition =
        some (.val (.word observed)) → observed ≠ 0 → 0 < remaining count state ∧
        (state.clock ≠ 0 → let output := evaluateHOLFiniteState (decClockHOLFinite state) loopBody
          (output.1 = none ∨ output.1 = some .continue) →
            CurrentCounter count output.2 ∧ remaining count output.2 < remaining count state) := by
    intro state codeEq valid observed read nonzero
    obtain ⟨current, cell, countCell, bound⟩ := valid
    have expected := condition_read state current.toNat count (by omega) small
      (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using cell) countCell
    have active : current.toNat < count := by
      by_cases active : current.toNat < count
      · exact active
      · rw [if_neg active] at expected
        have same : observed = 0#64 := by
          simpa only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using read.symm.trans expected
        exact (nonzero same).elim
    have before : remaining count state = count - current.toNat := by
      simp [remaining, CounterFlow.counterWord, cell, valueWord]
    refine ⟨by rw [before]; omega, ?_⟩
    intro funded
    dsimp only
    intro continuing
    let output := evaluateHOLFiniteState (decClockHOLFinite state) loopBody
    have summary := loop_local.summary_full (decClockHOLFinite state)
    unfold LocalSummary at summary
    have normal : output.1 = none := by
      rcases continuing with normal | continued
      · exact normal
      · exact (summary.2.2.2 continued).elim
    have run : evaluateHOLFiniteState (decClockHOLFinite state) loopBody = (none, output.2) := Prod.ext normal rfl
    have nextCell := loop_advance (decClockHOLFinite state) output.2 current cell run
    have nextCount := (summary.1 normal).trans countCell
    have number : (current + 1#64).toNat = current.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by change current.toNat + 1 < 2 ^ 64; omega)]
      rfl
    have after : remaining count output.2 = count - (current.toNat + 1) := by
      simp [remaining, CounterFlow.counterWord, nextCell, valueWord, number]
    refine ⟨⟨current + 1#64, nextCell, nextCount, by rw [number]; omega⟩, ?_⟩
    rw [after, before]
    omega
  have priced := ClockCost.ranked_loop source.code condition loopBody 2 (CurrentCounter count)
    (remaining count) (loop_body_cost source.code installed) progress source rfl ⟨word, counter, limit, bounded⟩
  rw [loop_shape]
  simpa only [remaining, CounterFlow.counterWord, counter, Option.getD_some, valueWord] using priced

theorem tail_cost (code) (installed : OriginalCode.Installed code) : ClockCost.Bound code tailCode 1 :=
  ClockCost.sequence code _ _ 1 0
    (ClockCost.conditional code _ _ _ 1 0 (failure_cost code installed _) (ClockCost.skip code))
    (ClockCost.returned code _)

/-- Bound every actual validator outcome from the current small count alone;
failed array reads and exceptions require no future memory model. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (count : Nat)
    (small : count ≤ 8) (installed : OriginalCode.Installed source.code)
    (limit : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 count)))) :
    source.clock - (evaluateHOLFiniteState source body).2.clock ≤ 3 * count + 1 := by
  let first : ProgHOL 64 := .ite (.cmp .equal (localVar "n") (.const 0#64)) returnZero .skip
  have decision : PureDecision first := .ite _ (.returned _) .skip
  have front := ClockCost.of_quiet source.code first (decision.quiet source.code) source rfl
  have back : ∀ middle, evaluateHOLFiniteState source first = (none, middle) →
      middle.clock - (evaluateHOLFiniteState middle
        (.dec (ofString "i") .one (.const 0#64) (.seq loop tailCode))).2.clock ≤ 3 * count + 1 := by
    intro middle normal
    have summary := decision.summary source
    rw [normal] at summary
    have same : middle = source := summary.1 rfl
    subst middle
    apply ClockCost.declared_current source "i" (.const 0#64) 0#64 (.seq loop tailCode) (3 * count + 1) rfl
    let ready := bind source "i" 0#64
    have saved : ready.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 count))) :=
      (bind_lookup_other source "i" "n" 0#64 (by decide)).trans limit
    have price := loop_cost ready count 0#64 small installed (bind_lookup_same _ _ _) saved (by simp)
    have whole := ClockCost.sequence_current ready loop tailCode (3 * count) 1
      (by simpa using price) (tail_cost ready.code installed)
    exact whole
  have price := ClockCost.sequence_reached_current source first
    (.dec (ofString "i") .one (.const 0#64) (.seq loop tailCode)) 0 (3 * count + 1) front back
  rw [body_shape]
  simpa only [Nat.zero_add, first] using price

end InitECandidate.Solver.Input.Offsets

#print axioms InitECandidate.Solver.Input.Offsets.failure_body_cost
#print axioms InitECandidate.Solver.Input.Offsets.failure_cost
#print axioms InitECandidate.Solver.Input.Offsets.loop_local
#print axioms InitECandidate.Solver.Input.Offsets.loop_advance
#print axioms InitECandidate.Solver.Input.Offsets.loop_body_cost
#print axioms InitECandidate.Solver.Input.Offsets.loop_cost
#print axioms InitECandidate.Solver.Input.Offsets.tail_cost
#print axioms InitECandidate.Solver.Input.Offsets.body_cost
