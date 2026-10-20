import Flapjack.Pancake.Semantics.PanProps.EvaluateClockSubAssembly

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Remove funded unused clock from an actual canonical evaluator run.
All memory, global and FFI-event fields remain those of that real run. -/
theorem evaluation_clock_sub {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (program : ProgHOL 64) (result : Option (PanSemResultExact 64)) (padding : Nat)
    (run : evaluateHOLFiniteState source program = (result,post))
    (enough : padding ≤ post.clock) (notTimeout : result ≠ some .timeOut) :
    evaluateHOLFiniteState {source with clock := source.clock - padding} program = (result,{post with clock := post.clock - padding}) := by
  let target := {post with clock := post.clock - padding}
  have restored : {target with clock := target.clock + padding} = post := by
    change {post with clock := post.clock - padding + padding} = post
    rw [Nat.sub_add_cancel enough]
  have encoded : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair (PanPropsEvalStateFiniteExact.ofPanSemFinite source) program =
      (result,{PanPropsEvalStateFiniteExact.ofPanSemFinite target with clock := target.clock + padding}) := by
    change PanPropsEvalStateFiniteExact.evaluateHOLFinitePair (PanPropsEvalStateFiniteExact.ofPanSemFinite source) program =
      (result,PanPropsEvalStateFiniteExact.ofPanSemFinite {target with clock := target.clock + padding})
    rw [restored]
    simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite,run]
  have lowered := evaluateClockSubHOLFinite program (PanPropsEvalStateFiniteExact.ofPanSemFinite source) result (PanPropsEvalStateFiniteExact.ofPanSemFinite target) padding encoded notTimeout
  have decoded := congrArg (fun output => (output.1,PanPropsEvalStateFiniteExact.toPanSemFinite output.2)) lowered
  simpa only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite,
    PanPropsEvalStateFiniteExact.ofPanSemFinite,PanPropsEvalStateFiniteExact.toPanSemFinite] using decoded

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.evaluation_clock_sub
