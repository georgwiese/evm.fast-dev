import InitECandidate.Solver.Input.CurrentTable.NodeBuild.HashState
import InitECandidate.Solver.Input.CurrentTable.NodeBuild.SetState
import InitECandidate.Solver.Input.ClockCostCurrent
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- The actual hash, ignored insertion and counter assignment all belong
to this one iteration. Stopped/error/short-clock outcomes are included. -/
theorem iteration_cost (data : Data) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : State data origin source index) (layout : Layout data) (inside : index<data.total) :
    source.clock-(evaluateHOLFiniteState source iteration).2.clock≤44*((data.lengths index).toNat/136)+1506 := by
  have combined := ClockCost.sequence_reached_current source hashCall (.seq setCall increment)
    (44*((data.lengths index).toNat/136)+690) 816 (hash_cost data origin source index state layout inside) (by
      intro middle normal
      have next := hash_normal data origin source middle index state layout inside normal
      have tail := ClockCost.sequence_current middle setCall increment 816 0 (set_cost data origin middle index next layout inside)
        (ClockCost.assign middle.code (ofString "i") _)
      simpa only [Nat.add_zero] using tail)
  change source.clock-(evaluateHOLFiniteState source iteration).2.clock≤_ at combined
  omega

theorem iteration_normal (data : Data) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : State data origin source index) (layout : Layout data) (inside : index<data.total)
    (run : evaluateHOLFiniteState source iteration=(none,post)) : State data origin post (index+1) := by
  obtain ⟨middle,hashRun,tailRun⟩ := sequence_none source post hashCall (.seq setCall increment) run
  exact set_increment_normal data origin middle post index (hash_normal data origin source middle index state layout inside hashRun) layout inside tailRun

/-- The ignored callees cannot escape the enclosing loop by break/continue
or return; the only direct body assignment changes i. -/
theorem iteration_local : LocalPrefix (ofString "n") iteration :=
  .seq (.call none _ _ (by intro name impossible; cases impossible))
    (.seq (.call none _ _ (by intro name impossible; cases impossible))
      (.assign (ofString "i") _ (by decide)))

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.iteration_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.iteration_normal
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.iteration_local
