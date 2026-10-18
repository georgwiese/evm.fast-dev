import InitECandidate.Solver.Input.EvaluationFields

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- An escaping exception from an actual ignored call came from its real
callee, after successful argument/code lookup and a positive caller clock.
This is the abnormal counterpart of ignored_data. -/
theorem ignored_exception_data (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (function : MlS) (arguments : List (ExpHOL 64))
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.call (some (none, none)) function arguments) = (some (.exception identifier payload), post)) :
    1 ≤ source.clock ∧ ∃ values body callee returnShape target,
      evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values ∧
      lookupCodeHOLFinite source.code.lookup function values = some (body, callee, returnShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = (some (.exception identifier payload), target) ∧
      post = emptyLocalsHOLFinite target ∧ target.memaddrs = source.memaddrs ∧ target.be = source.be ∧
      target.eshapes = source.eshapes ∧ target.code = source.code := by
  classical
  rw [evaluateHOLFiniteState_call] at run
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
          | returned returned => simp only at run; split at run <;> cases run
          | exception actualId actualPayload =>
            simp only at run
            have resultEq := congrArg Prod.fst run
            have payloadEq : actualId = identifier ∧ actualPayload = payload := by
              simpa only [Option.some.injEq, PanSemResultExact.exception.injEq] using resultEq
            rcases payloadEq with ⟨rfl, rfl⟩
            have same := congrArg Prod.snd run
            have fields := evaluation_fields (callEntryStateHOLFinite source callee) target body (some (.exception actualId actualPayload)) bodyRun
            exact ⟨by omega, values, body, callee, returnShape, target, rfl, called, bodyRun, same.symm,
              fields.1, fields.2.1, fields.2.2.1, fields.2.2.2⟩
          | error => cases run
          | timeOut => cases run
          | «break» => cases run
          | «continue» => cases run
          | finalFfi event => cases run

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.ignored_exception_data
