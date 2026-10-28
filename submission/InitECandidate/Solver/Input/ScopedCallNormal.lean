import InitECandidate.Solver.Input.CallResume
import Guest.Model

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- Actual scoped call with known entry arguments/code: derive funding,
the real callee return/shape checks and the actual resumed continuation. -/
theorem scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values)
    (called : lookupCodeHOLFinite source.code.lookup function values = some (body, callee, returnShape))
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (Flapjack.Basis.Pure.MlString.ofString name) shape function arguments continuation) = (some (.returned value), post)) :
    1 ≤ source.clock ∧ ∃ target returned inner,
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = (some (.returned returned), target) ∧
      (shapeEqHOL (shapeOfHOLExact returned) shape && shapeEqHOL (shapeOfHOLExact returned) returnShape) = true ∧
      evaluateHOLFiniteState (continuationEntry source target name returned) continuation = (some (.returned value), inner) ∧
      post = restore source name inner := by
  classical
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at normal
  simp only [args, called] at normal
  by_cases zero : source.clock = 0
  · rw [if_pos zero] at normal
    cases normal
  · rw [if_neg zero] at normal
    generalize bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at normal
    obtain ⟨result, target⟩ := output
    cases result with
    | none => cases normal
    | some result =>
      cases result with
      | returned returned =>
        simp only at normal
        split at normal
        · rename_i valid
          have resultEq := congrArg Prod.fst normal
          have postEq := congrArg Prod.snd normal
          exact ⟨by omega, target, returned, (evaluateHOLFiniteState (continuationEntry source target name returned) continuation).2,
            rfl, valid, Prod.ext resultEq rfl, postEq.symm⟩
        · cases normal
      | error => cases normal
      | timeOut => cases normal
      | «break» => cases normal
      | «continue» => cases normal
      | exception identifier payload => cases normal
      | finalFfi event => cases normal

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.scoped_normal
