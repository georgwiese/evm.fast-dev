import InitECandidate.Solver.Input.LocalEffectsScoped
import InitECandidate.Solver.Input.ScopedCallData

namespace InitECandidate.Solver.Input.LocalEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Reach the actual continuation of a nonlocal-preserving scoped helper.
Its clock is genuinely lower and its returned value is genuinely checked;
the full caller state differs only by clock and the new local binding.
The helper's quantitative price remains a separate obligation. -/
theorem pure_scoped_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (calleePure : ∀ values body callee returnShape,
      lookupCodeHOLFinite source.code.lookup function values = some (body, callee, returnShape) → Preserves source.code body)
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation) = (some (.returned value), post)) :
    ∃ clock returned inner, clock < source.clock ∧ shapeEqHOL (shapeOfHOLExact returned) shape = true ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) returned {source with clock := clock}) continuation = (some (.returned value), inner) ∧
      post = WitnessRadix.QueryBranch.restore source name inner := by
  obtain ⟨positive, values, body, callee, returnShape, target, returned, inner, args, called, bodyRun, checked, continuationRun, postEq⟩ :=
    CallNormal.scoped_data source post name shape function arguments continuation value normal
  have frame := calleePure values body callee returnShape called (callEntryStateHOLFinite source callee) rfl
  rw [bodyRun] at frame
  change erase target = erase source at frame
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    {state with locals := source.locals, clock := target.clock}) frame
  have nextEq : CallNormal.continuationEntry source target name returned =
      setVarHOLFinite (ofString name) returned {source with clock := target.clock} :=
    congrArg (setVarHOLFinite (ofString name) returned) callerFrame
  rw [nextEq] at continuationRun
  have targetClock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
  rw [bodyRun] at targetClock
  change target.clock ≤ source.clock - 1 at targetClock
  exact ⟨target.clock, returned, inner, by omega, (Bool.and_eq_true_iff.mp checked).1, continuationRun, postEq⟩

end InitECandidate.Solver.Input.LocalEffects

#print axioms InitECandidate.Solver.Input.LocalEffects.pure_scoped_prefix
