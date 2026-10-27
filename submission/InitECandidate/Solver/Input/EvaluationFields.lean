import Flapjack.Pancake.Semantics.PanProps.EvalInvariant
import Guest.Model

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Canonical evaluator invariants transported through the field-for-field
PanProps codec. Applies to every outcome, without success or code assumptions. -/
theorem evaluation_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (program : ProgHOL 64)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source program=(result,target)) :
    target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.eshapes=source.eshapes ∧ target.code=source.code := by
  have encoded : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair (PanPropsEvalStateFiniteExact.ofPanSemFinite source) program=
      (result,PanPropsEvalStateFiniteExact.ofPanSemFinite target) := by
    simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite,run]
  have fields:=evaluateInvariantsHOLFinite program (PanPropsEvalStateFiniteExact.ofPanSemFinite source) result
    (PanPropsEvalStateFiniteExact.ofPanSemFinite target) encoded
  exact ⟨fields.1,fields.2.2.1,fields.2.2.2.1,fields.2.2.2.2.2.2.1⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.evaluation_fields
