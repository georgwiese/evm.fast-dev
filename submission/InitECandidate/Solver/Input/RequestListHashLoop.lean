import InitECandidate.Solver.Input.RequestListHashStep
import InitECandidate.Solver.Input.ClockCostTerminatingLoop
import InitECandidate.Solver.Input.LoopInvariant

namespace InitECandidate.Solver.Input.RequestListHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual original request-record loop costs one selected fixed hash
and one loop tick per record. Its rank uses the current decoded count and
real counter; all observed non-timeout failing prefixes are retained. -/
theorem loop_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out cursor stp accel chunk zeros : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n) (actual : RoundState source kind p roots out cursor stp accel chunk zeros n index) (geometry : Geometry kind p roots cursor n)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source loop=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤(kind.record.price+2)*(n-index) := by
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → valid kind p roots out cursor stp accel chunk zeros n current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=some (.val (.word word)) → word≠0 → current.clock≠0 →
      let output:=evaluateHOLFiniteState (decClockHOLFinite current) step
      output.1≠some .timeOut → current.clock-output.2.clock≤remaining kind n current ∧
        ((output.1=none ∨ output.1=some .continue) → valid kind p roots out cursor stp accel chunk zeros n output.2 ∧
          current.clock-output.2.clock+remaining kind n output.2≤remaining kind n current) := by
    intro current codeEq currentValid word read nonzero funded
    obtain ⟨position,positionBound,ready⟩ := currentValid
    have active := active_of_test current kind p roots out cursor stp accel chunk zeros n position bounded positionBound ready word read nonzero
    let output := evaluateHOLFiniteState (decClockHOLFinite current) step
    dsimp only
    intro bodyNotTimeout
    have currentAllowance := remaining_read current kind p roots out cursor stp accel chunk zeros n position bounded positionBound ready
    have bodyPrice := chain_cost kinds (decClockHOLFinite current) output.2 kind p roots out cursor stp accel chunk zeros n position active
      (RoundState.dec_clock current kind p roots out cursor stp accel chunk zeros n position ready) geometry output.1 rfl bodyNotTimeout
    rw [selected_price] at bodyPrice
    change current.clock-1-output.2.clock≤kind.record.price+1 at bodyPrice
    have bodyClock := evaluateHOLFiniteState_clock_le (decClockHOLFinite current) step
    change output.2.clock≤current.clock-1 at bodyClock
    have amortized := allowance_step (kind.record.price+2) n position active
    have stopped : current.clock-output.2.clock≤remaining kind n current := by rw [currentAllowance]; omega
    refine ⟨stopped,?_⟩
    intro continuing
    have summary := (chain_local (ofString "p") kinds (by decide)).summary_full (decClockHOLFinite current)
    unfold LocalSummary at summary
    have normal : output.1=none := continuing.resolve_right summary.2.2.2
    have bodyRun : evaluateHOLFiniteState (decClockHOLFinite current) step=(none,output.2) := Prod.ext normal rfl
    have next := step_normal (decClockHOLFinite current) output.2 kind p roots out cursor stp accel chunk zeros n position active
      (RoundState.dec_clock current kind p roots out cursor stp accel chunk zeros n position ready) geometry bodyRun
    have nextBound : position+1≤n := by omega
    have nextAllowance := remaining_read output.2 kind p roots out cursor stp accel chunk zeros n (position+1) bounded nextBound next
    refine ⟨⟨position+1,nextBound,next⟩,?_⟩
    change current.clock-output.2.clock+remaining kind n output.2≤remaining kind n current
    rw [currentAllowance,nextAllowance]
    omega
  have observed : (evaluateHOLFiniteState source (.while test step)).1≠some .timeOut := by change (evaluateHOLFiniteState source loop).1≠_; rw [run]; exact notTimeout
  have price := ClockCost.potential_loop_terminating source.code test step (valid kind p roots out cursor stp accel chunk zeros n) (remaining kind n) priced source rfl ⟨index,inside,actual⟩ observed
  change source.clock-(evaluateHOLFiniteState source loop).2.clock≤remaining kind n source at price
  rw [run,remaining_read source kind p roots out cursor stp accel chunk zeros n index bounded inside actual] at price
  exact price

/-- The same real normal loop exit retains the actual bounded counter,
current workspace and temporary heap; no future loop outcome is supplied. -/
theorem loop_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind) (p roots out cursor stp accel chunk zeros : BitVec 64) (n index : Nat)
    (bounded : n≤134217728) (inside : index≤n) (actual : RoundState source kind p roots out cursor stp accel chunk zeros n index) (geometry : Geometry kind p roots cursor n)
    (run : evaluateHOLFiniteState source loop=(none,post)) : valid kind p roots out cursor stp accel chunk zeros n post := by
  have transition : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → valid kind p roots out cursor stp accel chunk zeros n current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=some (.val (.word word)) → word≠0 → current.clock≠0 → ∀ target,
      evaluateHOLFiniteState (decClockHOLFinite current) step=(none,target) → valid kind p roots out cursor stp accel chunk zeros n target := by
    intro current codeEq currentValid word read nonzero funded target bodyRun
    obtain ⟨position,positionBound,ready⟩ := currentValid
    have active := active_of_test current kind p roots out cursor stp accel chunk zeros n position bounded positionBound ready word read nonzero
    have next := step_normal (decClockHOLFinite current) target kind p roots out cursor stp accel chunk zeros n position active
      (RoundState.dec_clock current kind p roots out cursor stp accel chunk zeros n position ready) geometry bodyRun
    exact ⟨position+1,by omega,next⟩
  exact loop_invariant source.code (ofString "p") test step (chain_local (ofString "p") kinds (by decide))
    (valid kind p roots out cursor stp accel chunk zeros n) transition source post rfl ⟨index,inside,actual⟩ run

theorem loop_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code loop :=
  GlobalEffects.loop key code test step (chain_globals kinds key code installed different)

theorem loop_local (key : MlS) (different : key≠ofString "i") : LocalPrefix key loop := .loop test (chain_local key kinds different)

end InitECandidate.Solver.Input.RequestListHash

#print axioms InitECandidate.Solver.Input.RequestListHash.loop_cost
#print axioms InitECandidate.Solver.Input.RequestListHash.loop_normal
#print axioms InitECandidate.Solver.Input.RequestListHash.loop_globals
#print axioms InitECandidate.Solver.Input.RequestListHash.loop_local
