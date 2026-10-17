import InitECandidate.Solver.Input.NormalCallEntry

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Invert any genuine normal scoped call, without assuming argument or code
lookup success. Its actual returned value enters the continuation with caller
locals restored; code/domain/exception shapes retain the canonical invariants. -/
theorem normal_data (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation) =
      (some (.returned value), post)) :
    ∃ values calleeBody callee returnShape calleePost returned inner,
      evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values ∧
      lookupCodeHOLFinite source.code.lookup function values = some (calleeBody, callee, returnShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) calleeBody = (some (.returned returned), calleePost) ∧
      evaluateHOLFiniteState (continuationEntry source calleePost name returned) continuation =
        (some (.returned value), inner) ∧
      post = restore source name inner ∧
      calleePost.memaddrs = source.memaddrs ∧ calleePost.be = source.be ∧
      calleePost.eshapes = source.eshapes ∧ calleePost.code = source.code ∧
      shapeEqHOL (shapeOfHOLExact returned) shape = true := by
  classical
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at run
  cases args : evalListHOLFinite source
      (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args] at run; cases run
  | some values =>
    simp only [args] at run
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called] at run; cases run
    | some data =>
      obtain ⟨body, callee, returnShape⟩ := data
      simp only [called] at run
      by_cases zero : source.clock = 0
      · rw [if_pos zero] at run
        cases run
      · rw [if_neg zero] at run
        generalize bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at run
        obtain ⟨result, target⟩ := output
        cases result with
        | none => cases run
        | some result =>
          cases result with
          | returned returned =>
            simp only at run
            by_cases valid : (shapeEqHOL (shapeOfHOLExact returned) shape &&
                shapeEqHOL (shapeOfHOLExact returned) returnShape) = true
            · rw [if_pos valid] at run
              let ready := continuationEntry source target name returned
              let inner := (evaluateHOLFiniteState ready continuation).2
              have resultEq := congrArg Prod.fst run
              have postEq := congrArg Prod.snd run
              have fields := evaluation_fields (callEntryStateHOLFinite source callee) target body
                (some (.returned returned)) bodyRun
              refine ⟨values, body, callee, returnShape, target, returned, inner, rfl, called, bodyRun, ?_, ?_, fields.1, fields.2.1,
                fields.2.2.1, fields.2.2.2, (Bool.and_eq_true_iff.mp valid).1⟩
              · exact Prod.ext resultEq rfl
              · exact postEq.symm
            · rw [if_neg valid] at run
              cases run
          | error => cases run
          | timeOut => cases run
          | «break» => cases run
          | «continue» => cases run
          | exception identifier payload => cases run
          | finalFfi event => cases run

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.normal_data
