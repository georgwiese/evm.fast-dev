import InitECandidate.Solver.Input.ProgressiveLoop
import InitECandidate.Solver.Input.ProgressiveSuffixCost

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Actual chunk loop plus the complete original root-fold/output suffix.
The continuing loop derives its root count and current workspace, while
all escaping outcomes pay only the prefix they really executed. -/
theorem dense_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros stp accel acc out : BitVec 64) (n k : Nat)
    (bounded : n≤134217728) (inside : k≤15) (actual : RoundState source p roots cursor zeros stp accel n k) (mapped : Geometry p roots cursor zeros n)
    (accumulator : source.locals.lookup (ofString "acc")=some (.val (.word acc)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (accArena : AllocatedBytes.Arena acc 32) (outArena : AllocatedBytes.Arena out 32) (aligned : acc.toNat%8=0)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source loopAndSuffix=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤allowance n (offset k) k+818 := by
  rw [fold_shape.2.2.1] at run
  apply ClockCost.sequence_terminating source post loop afterLoop (allowance n (offset k) k) 818
    (fun result target continued notTimeout=>loop_cost source target p roots cursor zeros stp accel n k bounded inside actual mapped result continued notTimeout) _ result run notTimeout
  intro middle normal result target continued notTimeout
  obtain ⟨nextK,nextBound,next⟩ := loop_normal source middle p roots cursor zeros stp accel n k bounded inside actual mapped normal
  have other (name : String) (a : ofString name≠ofString "cnt") (b : ofString name≠ofString "off") (c : ofString name≠ofString "size") (d : ofString name≠ofString "k") :
      middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    have safe : LocalPrefix (ofString name) loop := by rw [loop_shape.1]; exact .loop _ (step_other (ofString name) a b c d)
    have summary := safe.summary_full source
    unfold LocalSummary at summary
    rw [normal] at summary
    exact summary.1 rfl
  have price := suffix_cost middle roots acc out stp accel nextK nextBound next.workspace next.rootsLocal
    ((other "acc" (by decide) (by decide) (by decide) (by decide)).trans accumulator)
    ((other "out" (by decide) (by decide) (by decide) (by decide)).trans output) next.round mapped.rootsArena accArena outArena aligned
  rw [continued] at price
  change middle.clock-target.clock≤54*nextK+8 at price
  omega

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.dense_cost
