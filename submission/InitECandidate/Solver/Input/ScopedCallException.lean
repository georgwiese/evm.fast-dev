import InitECandidate.Solver.Input.ScopedCallData

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- An actual escaping exception from a scoped call comes either from its
real callee or from the real continuation after a checked return. Arguments,
code lookup and caller funding are derived in both cases. -/
theorem scoped_exception_data (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation) =
      (some (.exception identifier payload), post)) :
    1 ≤ source.clock ∧ ∃ values body callee returnShape target,
      evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values ∧
      lookupCodeHOLFinite source.code.lookup function values = some (body, callee, returnShape) ∧
      ((evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = (some (.exception identifier payload), target) ∧
        post = emptyLocalsHOLFinite target) ∨
       ∃ returned inner,
        evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = (some (.returned returned), target) ∧
        (shapeEqHOL (shapeOfHOLExact returned) shape && shapeEqHOL (shapeOfHOLExact returned) returnShape) = true ∧
        evaluateHOLFiniteState (continuationEntry source target name returned) continuation = (some (.exception identifier payload), inner) ∧
        post = restore source name inner) := by
  classical
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at run
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
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
            split at run
            · rename_i valid
              have resultEq := congrArg Prod.fst run
              have postEq := congrArg Prod.snd run
              exact ⟨by omega, values, body, callee, returnShape, target, rfl, called, Or.inr
                ⟨returned, (evaluateHOLFiniteState (continuationEntry source target name returned) continuation).2,
                  bodyRun, valid, Prod.ext resultEq rfl, postEq.symm⟩⟩
            · cases run
          | exception actualId actualPayload =>
            simp only at run
            have resultEq := congrArg Prod.fst run
            have payloadEq : actualId = identifier ∧ actualPayload = payload := by
              simpa only [Option.some.injEq, PanSemResultExact.exception.injEq] using resultEq
            rcases payloadEq with ⟨rfl, rfl⟩
            have postEq := congrArg Prod.snd run
            exact ⟨by omega, values, body, callee, returnShape, target, rfl, called, Or.inl ⟨bodyRun, postEq.symm⟩⟩
          | error => cases run
          | timeOut => cases run
          | «break» => cases run
          | «continue» => cases run
          | finalFfi event => cases run

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.scoped_exception_data
