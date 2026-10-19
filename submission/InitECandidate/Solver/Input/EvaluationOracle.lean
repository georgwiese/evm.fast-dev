import InitECandidate.Solver.Input.EvaluationFields

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- The actual source evaluator retains its oracle function on every
outcome, including executions that perform real external calls. -/
theorem evaluation_oracle (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (program : ProgHOL 64)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source program=(result,target)) :
    target.ffi.oracle=source.ffi.oracle := by
  have encoded : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair (PanPropsEvalStateFiniteExact.ofPanSemFinite source) program=
      (result,PanPropsEvalStateFiniteExact.ofPanSemFinite target) := by
    simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite,run]
  exact (evaluateInvariantsHOLFinite program (PanPropsEvalStateFiniteExact.ofPanSemFinite source) result
    (PanPropsEvalStateFiniteExact.ofPanSemFinite target) encoded).2.2.2.2.2.2.2

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.evaluation_oracle
