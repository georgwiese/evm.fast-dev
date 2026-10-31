import InitECandidate.Solver.Headers.CurrentValidate.Control
import InitECandidate.Solver.Input.ClockCostPotentialLoop
import InitECandidate.Solver.Input.LoopInvariant

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input

def DecodeValid (data : Data) (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ index,index≤data.count ∧ RoundState data origin current index

def decodeRemaining (data : Data) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  258497*(data.count-(CounterFlow.counterWord source (ofString "i")).toNat)

private theorem remaining_read (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (bounded : index≤data.count) :
    decodeRemaining data source=258497*(data.count-index) := by
  have small : index<2^64 := by have h:=layout.count; omega
  simp [decodeRemaining,CounterFlow.counterWord,state.indexCell,valueWord,BitVec.toNat_ofNat]
  omega

/-- Every actual first-loop outcome is bounded, including failed decoding,
allocation, stores and hashing. Only a genuine continuing iteration supplies
the next row state and consumes one remaining row allowance. -/
theorem decode_loop_cost (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (bounded : index≤data.count) :
    source.clock-(evaluateHOLFiniteState source (.while test decodeStep)).2.clock≤258497*(data.count-index) := by
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → DecodeValid data origin current → ∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word)) → word≠0 → current.clock≠0 →
      let output:=evaluateHOLFiniteState (decClockHOLFinite current) decodeStep
      current.clock-output.2.clock≤decodeRemaining data current ∧
        ((output.1=none ∨ output.1=some .continue) → DecodeValid data origin output.2 ∧
          current.clock-output.2.clock+decodeRemaining data output.2≤decodeRemaining data current) := by
    intro current codeEq ready word read nonzero funded
    obtain ⟨position,positionBound,currentState⟩:=ready
    have active:=active_of_test data origin current position currentState layout (by omega) word read nonzero
    have entered:=currentState.dec_clock data origin current position
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) decodeStep
    have cost:=Nat.le_trans (decode_step_cost data origin (decClockHOLFinite current) position entered layout active) (decode_price_limit data layout position active)
    have clock:=evaluateHOLFiniteState_clock_le (decClockHOLFinite current) decodeStep
    change current.clock-1-output.2.clock≤258496 at cost
    change output.2.clock≤current.clock-1 at clock
    have allowance:=remaining_read data origin current position currentState layout positionBound
    dsimp only
    change current.clock-output.2.clock≤decodeRemaining data current ∧ _
    refine ⟨by rw [allowance]; omega,?_⟩
    intro continuing
    have safe:=decode_step_local.summary_full (decClockHOLFinite current)
    unfold LocalSummary at safe
    have normal : output.1=none := continuing.resolve_right safe.2.2.2
    have actual : evaluateHOLFiniteState (decClockHOLFinite current) decodeStep=(none,output.2) := Prod.ext normal rfl
    have next:=decode_step_normal data origin (decClockHOLFinite current) output.2 position entered layout active actual
    have nextAllowance:=remaining_read data origin output.2 (position+1) next layout (by omega)
    refine ⟨⟨position+1,by omega,next⟩,?_⟩
    rw [allowance,nextAllowance]
    dsimp only [output] at cost clock ⊢
    omega
  have price:=ClockCost.potential_loop source.code test decodeStep (DecodeValid data origin) (decodeRemaining data) step source rfl ⟨index,bounded,state⟩
  rw [remaining_read data origin source index state layout bounded] at price
  exact price

theorem decode_loop_normal (data : Data) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (bounded : index≤data.count)
    (normal : evaluateHOLFiniteState source (.while test decodeStep)=(none,post)) : DecodeValid data origin post := by
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → DecodeValid data origin current → ∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word)) → word≠0 → current.clock≠0 → ∀ target,
      evaluateHOLFiniteState (decClockHOLFinite current) decodeStep=(none,target) → DecodeValid data origin target := by
    intro current codeEq ready word read nonzero funded target bodyRun
    obtain ⟨position,positionBound,currentState⟩:=ready
    have active:=active_of_test data origin current position currentState layout (by omega) word read nonzero
    have next:=decode_step_normal data origin (decClockHOLFinite current) target position (currentState.dec_clock data origin current position) layout active bodyRun
    exact ⟨position+1,by omega,next⟩
  exact Input.loop_invariant source.code (ofString "n") test decodeStep decode_step_local (DecodeValid data origin) step source post rfl ⟨index,bounded,state⟩ normal

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.decode_loop_cost
#print axioms InitECandidate.Solver.Headers.CurrentValidate.decode_loop_normal
