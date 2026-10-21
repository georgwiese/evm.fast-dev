import InitECandidate.Solver.Headers.ValidateLinkStep
import InitECandidate.Solver.Headers.ValidateDecodeControl
import InitECandidate.Solver.Input.LoopInvariantNoControl

namespace InitECandidate.Solver.Headers.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def LinkValid (data : Data) (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ index,index≤data.count+1 ∧ RoundState data origin current index
def linkRank (data : Data) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  data.count-(Input.CounterFlow.counterWord source (ofString "i")).toNat

theorem link_rank_read (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (bounded : index≤data.count+1) : linkRank data source=data.count-index := by
  have small : index<18446744073709551616 := by have h:=layout.count; omega
  simp [linkRank,Input.CounterFlow.counterWord,state.indexCell,valueWord,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]

/-- Actual second-loop calls include early comparison/read failures. Only
normal continued iterations advance their real counter, and all outcomes
fit130 source ticks per remaining original header link. -/
theorem link_loop_cost (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (bounded : index≤data.count+1) :
    source.clock-(evaluateHOLFiniteState source (.while test linkStep)).2.clock≤130*(data.count-index) := by
  have bodyPrice : Input.ClockCost.Bound source.code linkStep 129 := by
    intro current codeEq
    exact link_step_cost current (by rw [codeEq]; exact state.installed)
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → LinkValid data origin current → ∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word)) → word≠0 →
      0<linkRank data current ∧ (current.clock≠0 → let output:=evaluateHOLFiniteState (decClockHOLFinite current) linkStep;
        (output.1=none ∨ output.1=some .continue) → LinkValid data origin output.2 ∧ linkRank data output.2<linkRank data current) := by
    intro current codeEq ready word read nonzero
    obtain ⟨position,positionBound,currentState⟩ := ready
    have active:=active_of_test data origin current position currentState layout positionBound word read nonzero
    have rankEq:=link_rank_read data origin current position currentState layout positionBound
    refine ⟨by rw [rankEq]; omega,?_⟩
    intro funded
    dsimp only
    intro continuing
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) linkStep
    have normal : output.1=none := continuing.resolve_right (link_step_no_control (decClockHOLFinite current)).2
    have run : evaluateHOLFiniteState (decClockHOLFinite current) linkStep=(none,output.2) := Prod.ext normal rfl
    have next:=link_step_normal data origin (decClockHOLFinite current) output.2 position (currentState.dec_clock data origin current position) run
    have nextRank:=link_rank_read data origin output.2 (position+1) next layout (by omega)
    exact ⟨⟨position+1,by omega,next⟩,by rw [nextRank,rankEq]; omega⟩
  have price:=Input.ClockCost.ranked_loop source.code test linkStep 129 (LinkValid data origin) (linkRank data) bodyPrice progress source rfl ⟨index,bounded,state⟩
  rw [link_rank_read data origin source index state layout bounded] at price
  exact price

theorem link_loop_normal (data : Data) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data) (bounded : index≤data.count+1)
    (normal : evaluateHOLFiniteState source (.while test linkStep)=(none,post)) : LinkValid data origin post := by
  apply Input.loop_invariant_no_control source.code test linkStep link_step_no_control (LinkValid data origin) _ source post rfl ⟨index,bounded,state⟩ normal
  intro current codeEq ready word read nonzero funded target bodyRun
  obtain ⟨position,positionBound,currentState⟩ := ready
  have active:=active_of_test data origin current position currentState layout positionBound word read nonzero
  have next:=link_step_normal data origin (decClockHOLFinite current) target position (currentState.dec_clock data origin current position) bodyRun
  exact ⟨position+1,by omega,next⟩

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.link_rank_read
#print axioms InitECandidate.Solver.Headers.Validate.link_loop_cost
#print axioms InitECandidate.Solver.Headers.Validate.link_loop_normal
