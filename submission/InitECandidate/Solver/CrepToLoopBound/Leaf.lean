import InitECandidate.Solver.CrepToLoopBound.Common
import InitECandidate.Solver.CrepToLoopBound.LeafCost
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Assembly

namespace InitECandidate.Solver.CrepToLoopBound
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- The existing semantic simulation fixes both endpoint clocks. Straight-line
compiled code bounds their difference, hence the existential clock overhead. -/
theorem simulateLeaf {width : Nat} [NeZero width] {F : Type}
    (limit : Nat) (program : CrepProgHOL width) (source : CrepSemHOLState width F)
    (leaf : Leaf program = true) : Simulation limit program source := by
  intro safe bounded result post target context live run notError hs hm hg hc hl
  obtain ⟨extra, targetResult, targetFinal, targetRun, finalState, rest⟩ :=
    crepToLoopNcompileCorrectOf program source result post target context live
      run notError hs hm hg hc hl
  have shape := leafCost context live program leaf
  have consumed := straightClock (compileHOLExact context live program)
    { target with clock := target.clock + extra } shape.1
  rw [targetRun] at consumed
  have initialClock := hs.2.2.1
  have finalClock := finalState.2.2.1
  have decreasing := clockDecrease run
  refine ⟨extra, targetResult, targetFinal, ?_, targetRun, finalState, rest⟩
  dsimp only at consumed
  omega

end InitECandidate.Solver.CrepToLoopBound
#print axioms InitECandidate.Solver.CrepToLoopBound.simulateLeaf
