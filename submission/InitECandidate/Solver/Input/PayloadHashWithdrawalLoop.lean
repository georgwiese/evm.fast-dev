import InitECandidate.Solver.Input.PayloadHashWithdrawalStep
import InitECandidate.Solver.Input.ClockCostTerminatingLoop
import InitECandidate.Solver.Input.LoopInvariant

namespace InitECandidate.Solver.Input.PayloadHash.Withdrawals
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Original withdrawal loop costs617 source ticks per actual record,
including arbitrary non-timeout failing prefixes and real loop control. -/
theorem loop_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor stp accel chunk zeros : BitVec 64) (n index : Nat)
    (inside : index≤n) (actual : RoundState source p roots cursor stp accel chunk zeros n index) (geometry : Geometry p roots cursor n)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source withdrawalLoop=(result,post)) (notTimeout : result≠some .timeOut) : source.clock-post.clock≤617*(n-index) := by
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → valid p roots cursor stp accel chunk zeros n current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) withdrawalTest=some (.val (.word word)) → word≠0 → current.clock≠0 →
      let output:=evaluateHOLFiniteState (decClockHOLFinite current) withdrawalStep
      output.1≠some .timeOut → current.clock-output.2.clock≤remaining n current ∧
        ((output.1=none ∨ output.1=some .continue) → valid p roots cursor stp accel chunk zeros n output.2 ∧
          current.clock-output.2.clock+remaining n output.2≤remaining n current) := by
    intro current codeEq ready word read nonzero funded
    obtain ⟨position,positionBound,currentRound⟩ := ready
    have active := active_of_test current p roots cursor stp accel chunk zeros n position geometry.countBound positionBound currentRound word read nonzero
    have entryRound := RoundState.dec_clock current p roots cursor stp accel chunk zeros n position currentRound
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) withdrawalStep
    dsimp only
    intro bodyNotTimeout
    change current.clock-output.2.clock≤remaining n current ∧
      ((output.1=none ∨ output.1=some .continue) → valid p roots cursor stp accel chunk zeros n output.2 ∧
        current.clock-output.2.clock+remaining n output.2≤remaining n current)
    have cost : current.clock-1-output.2.clock≤616 := step_cost (decClockHOLFinite current) output.2 p roots cursor stp accel chunk zeros n position entryRound geometry active output.1 rfl bodyNotTimeout
    have monotone : output.2.clock≤current.clock-1 := evaluateHOLFiniteState_clock_le (decClockHOLFinite current) withdrawalStep
    have currentAllowance := remaining_read current p roots cursor stp accel chunk zeros n position geometry.countBound positionBound currentRound
    refine ⟨by rw [currentAllowance]; omega,?_⟩
    intro continuing
    have summary := (withdrawal_step_local (ofString "wd") (by decide)).summary_full (decClockHOLFinite current)
    unfold LocalSummary at summary
    have normal : output.1=none := continuing.resolve_right summary.2.2.2
    have bodyRun : evaluateHOLFiniteState (decClockHOLFinite current) withdrawalStep=(none,output.2) := Prod.ext normal rfl
    have next := step_normal (decClockHOLFinite current) output.2 p roots cursor stp accel chunk zeros n position entryRound geometry active bodyRun
    have nextAllowance := remaining_read output.2 p roots cursor stp accel chunk zeros n (position+1) geometry.countBound (by omega) next
    refine ⟨⟨position+1,by omega,next⟩,?_⟩
    rw [currentAllowance,nextAllowance]
    omega
  have observed : (evaluateHOLFiniteState source (.while withdrawalTest withdrawalStep)).1≠some .timeOut := by rw [←loop_shapes.2.2.1,run]; exact notTimeout
  have price := ClockCost.potential_loop_terminating source.code withdrawalTest withdrawalStep (valid p roots cursor stp accel chunk zeros n) (remaining n) priced source rfl ⟨index,inside,actual⟩ observed
  rw [←loop_shapes.2.2.1,run] at price
  change source.clock-post.clock≤remaining n source at price
  rw [remaining_read source p roots cursor stp accel chunk zeros n index geometry.countBound inside actual] at price
  exact price

theorem loop_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor stp accel chunk zeros : BitVec 64) (n index : Nat)
    (inside : index≤n) (actual : RoundState source p roots cursor stp accel chunk zeros n index) (geometry : Geometry p roots cursor n)
    (run : evaluateHOLFiniteState source withdrawalLoop=(none,post)) : valid p roots cursor stp accel chunk zeros n post := by
  have transition : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → valid p roots cursor stp accel chunk zeros n current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) withdrawalTest=some (.val (.word word)) → word≠0 → current.clock≠0 → ∀ target,
      evaluateHOLFiniteState (decClockHOLFinite current) withdrawalStep=(none,target) → valid p roots cursor stp accel chunk zeros n target := by
    intro current codeEq ready word read nonzero funded target bodyRun
    obtain ⟨position,positionBound,currentRound⟩ := ready
    have active := active_of_test current p roots cursor stp accel chunk zeros n position geometry.countBound positionBound currentRound word read nonzero
    have next := step_normal (decClockHOLFinite current) target p roots cursor stp accel chunk zeros n position
      (RoundState.dec_clock current p roots cursor stp accel chunk zeros n position currentRound) geometry active bodyRun
    exact ⟨position+1,by omega,next⟩
  rw [loop_shapes.2.2.1] at run
  exact loop_invariant source.code (ofString "wd") withdrawalTest withdrawalStep (withdrawal_step_local (ofString "wd") (by decide))
    (valid p roots cursor stp accel chunk zeros n) transition source post rfl ⟨index,inside,actual⟩ run

theorem loop_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code withdrawalLoop := by
  rw [loop_shapes.2.2.1]
  exact GlobalEffects.loop key code _ _ (withdrawal_step_globals key code installed different)

theorem loop_local (key : MlS) (different : key≠ofString "i") : LocalPrefix key withdrawalLoop := by
  rw [loop_shapes.2.2.1]
  exact .loop withdrawalTest (withdrawal_step_local key different)

end InitECandidate.Solver.Input.PayloadHash.Withdrawals

#print axioms InitECandidate.Solver.Input.PayloadHash.Withdrawals.loop_cost
#print axioms InitECandidate.Solver.Input.PayloadHash.Withdrawals.loop_normal
#print axioms InitECandidate.Solver.Input.PayloadHash.Withdrawals.loop_globals
#print axioms InitECandidate.Solver.Input.PayloadHash.Withdrawals.loop_local
