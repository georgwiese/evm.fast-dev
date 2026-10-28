import InitECandidate.Solver.Input.CurrentTable.NodeBuild.Control
import InitECandidate.Solver.Input.ClockCostPotentialLoop
import InitECandidate.Solver.Input.LoopInvariant
import Mathlib.Algebra.BigOperators.Intervals

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open scoped BigOperators

def LoopValid (data : Data) (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ index,index≤data.total ∧ State data origin current index

/-- Sum actual reached row lengths, rather than pricing every row at its
separate maximum length. Each row includes its real loop tick and insertion. -/
def remainingFrom (data : Data) (index : Nat) : Nat :=
  ∑ position ∈ Finset.Ico index data.total,(44*((data.lengths position).toNat/136)+1507)

def remaining (data : Data) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  remainingFrom data (CounterFlow.counterWord source (ofString "i")).toNat

private theorem remaining_read (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : State data origin source index) (layout : Layout data) (bounded : index≤data.total) :
    remaining data source=remainingFrom data index := by
  have small : index<2^64 := by have := layout.totalSmall; omega
  unfold remaining CounterFlow.counterWord
  rw [state.indexCell]
  change remainingFrom data (BitVec.ofNat 64 index).toNat=remainingFrom data index
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]

private theorem remaining_head (data : Data) (index : Nat) (active : index<data.total) :
    remainingFrom data index=44*((data.lengths index).toNat/136)+1507+remainingFrom data (index+1) := by
  simpa only [remainingFrom] using
    Finset.sum_eq_sum_Ico_succ_bot active (fun position=>44*((data.lengths position).toNat/136)+1507)

/-- Every original loop outcome fits the sum of real row allowances.
The invariant for the next row comes only from an actual completed hash,
insertion and increment; exhausted clocks and every earlier stop are covered. -/
theorem loop_cost (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : State data origin source index) (layout : Layout data) (bounded : index≤data.total) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤remainingFrom data index := by
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → LoopValid data origin current → ∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) condition=some (.val (.word word)) → word≠0 → current.clock≠0 →
      let output:=evaluateHOLFiniteState (decClockHOLFinite current) iteration
      current.clock-output.2.clock≤remaining data current ∧
        ((output.1=none ∨ output.1=some .continue) → LoopValid data origin output.2 ∧
          current.clock-output.2.clock+remaining data output.2≤remaining data current) := by
    intro current codeEq ready word read nonzero funded
    obtain ⟨position,positionBound,currentState⟩ := ready
    have active := active_of_test data origin current position currentState layout (by omega) word read nonzero
    have entered := currentState.dec_clock data origin current position
    let output := evaluateHOLFiniteState (decClockHOLFinite current) iteration
    have cost := iteration_cost data origin (decClockHOLFinite current) position entered layout active
    have clock := evaluateHOLFiniteState_clock_le (decClockHOLFinite current) iteration
    change current.clock-1-output.2.clock≤44*((data.lengths position).toNat/136)+1506 at cost
    change output.2.clock≤current.clock-1 at clock
    have allowance := (remaining_read data origin current position currentState layout positionBound).trans (remaining_head data position active)
    dsimp only
    change current.clock-output.2.clock≤remaining data current ∧ _
    refine ⟨by rw [allowance]; omega,?_⟩
    intro continuing
    have safe := iteration_local.summary_full (decClockHOLFinite current)
    unfold LocalSummary at safe
    have normal : output.1=none := continuing.resolve_right safe.2.2.2
    have actual : evaluateHOLFiniteState (decClockHOLFinite current) iteration=(none,output.2) := Prod.ext normal rfl
    have next := iteration_normal data origin (decClockHOLFinite current) output.2 position entered layout active actual
    have nextAllowance := remaining_read data origin output.2 (position+1) next layout (by omega)
    refine ⟨⟨position+1,by omega,next⟩,?_⟩
    rw [allowance,nextAllowance]
    dsimp only [output] at cost clock ⊢
    omega
  have price := ClockCost.potential_loop source.code condition iteration (LoopValid data origin) (remaining data) step source rfl ⟨index,bounded,state⟩
  rw [remaining_read data origin source index state layout bounded] at price
  exact price

/-- Normal loop exit retains the full actual table and input frame. -/
theorem loop_normal (data : Data) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : State data origin source index) (layout : Layout data) (bounded : index≤data.total)
    (normal : evaluateHOLFiniteState source loop=(none,post)) : LoopValid data origin post := by
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → LoopValid data origin current → ∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) condition=some (.val (.word word)) → word≠0 → current.clock≠0 → ∀ target,
      evaluateHOLFiniteState (decClockHOLFinite current) iteration=(none,target) → LoopValid data origin target := by
    intro current codeEq ready word read nonzero funded target bodyRun
    obtain ⟨position,positionBound,currentState⟩ := ready
    have active := active_of_test data origin current position currentState layout (by omega) word read nonzero
    have next := iteration_normal data origin (decClockHOLFinite current) target position (currentState.dec_clock data origin current position) layout active bodyRun
    exact ⟨position+1,by omega,next⟩
  exact Input.loop_invariant source.code (ofString "n") condition iteration iteration_local (LoopValid data origin) step source post rfl ⟨index,bounded,state⟩ normal

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.loop_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.loop_normal
