import InitECandidate.Solver.WitnessRadix.SortProperties

namespace InitECandidate.Solver.WitnessRadix.SortProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open QueryBranch

/-- Both actual index resets, the complete stable-scatter loop and the
complete copy loop, followed by an arbitrary continuation. -/
theorem execute {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst keys : BitVec 64)
    (keyFor : BitVec 64 → ByteKeys.Key) (input : List (BitVec 64)) (position start limit : Nat)
    (premises : Inputs source src dst keys keyFor input position start limit) (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (code continuation) =
      evaluateHOLFiniteState (sorted source src dst keyFor position start input) continuation := by
  classical
  have firstRun := reset_execute source _ premises.indexLocal
  have scatterRun := scattered_run source src dst keys keyFor input position start limit premises
  have secondRun := reset_execute (scattered source dst keyFor position start input) _
    (scattered_index source dst keyFor position start input)
  have copyRun := copied_run source src dst keys keyFor input position start limit premises
  have scatterClock : (scattered source dst keyFor position start input).clock = source.clock - input.length :=
    congrArg (fun state => state.clock) (scattered_frame source dst keyFor position start input)
  have copyClock : (sorted source src dst keyFor position start input).clock = source.clock - 2 * input.length :=
    congrArg (fun state => state.clock) (sorted_frame source src dst keyFor position start limit input premises.fits premises.allocation)
  rw [code, StateSteps.next_sequence source (first source) SplitProgram.resetIndex _ firstRun (Nat.le_refl _)]
  rw [StateSteps.next_sequence (first source) (scattered source dst keyFor position start input)
    ScatterProgram.scatterLoop _ scatterRun (by change _ ≤ source.clock; omega)]
  rw [StateSteps.next_sequence (scattered source dst keyFor position start input)
    (second source dst keyFor position start input) SplitProgram.resetIndex _ secondRun (Nat.le_refl _)]
  rw [StateSteps.next_sequence (second source dst keyFor position start input)
    (sorted source src dst keyFor position start input) BuildCopy.copyLoop continuation copyRun (by
      change _ ≤ (scattered source dst keyFor position start input).clock
      rw [scatterClock, copyClock]
      omega)]

end InitECandidate.Solver.WitnessRadix.SortProgram

#print axioms InitECandidate.Solver.WitnessRadix.SortProgram.execute
