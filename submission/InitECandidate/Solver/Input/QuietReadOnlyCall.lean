import InitECandidate.Solver.Input.LocalEffectsCall
import InitECandidate.Solver.Input.QuietClock
import InitECandidate.Solver.Input.IgnoredCallData
import InitECandidate.Solver.Input.IgnoredCallException

namespace InitECandidate.Solver.Input.QuietReadOnlyCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A genuine normal read-only zero-body-clock call pays exactly its one
caller clock. Its arguments/code/callee return are derived from the call. -/
theorem normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (function : MlS) (arguments : List (ExpHOL 64))
    (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL)
    (code : source.code.lookup function = some (formals, body, shape))
    (pureBody : LocalEffects.Preserves source.code body) (quiet : QuietClock.Preserves source.code body)
    (run : evaluateHOLFiniteState source (.call (some (none, none)) function arguments) = (none, post)) :
    1 ≤ source.clock ∧ post = {source with clock := source.clock - 1} := by
  obtain ⟨positive, values, actual, callee, returnShape, target, returned, args, called, bodyRun, checked, postEq, fields⟩ :=
    CallNormal.ignored_data source post function arguments run
  have identified := LocalEffects.lookup_body source.code function formals body shape code values actual callee returnShape called
  rw [identified] at bodyRun
  have frame := pureBody (callEntryStateHOLFinite source callee) rfl
  rw [bodyRun] at frame
  change LocalEffects.erase target = LocalEffects.erase source at frame
  have targetClock := quiet (callEntryStateHOLFinite source callee) rfl
  rw [bodyRun] at targetClock
  change target.clock = source.clock - 1 at targetClock
  have lifted := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    {state with locals := source.locals, clock := target.clock}) frame
  refine ⟨positive, ?_⟩
  rw [postEq]
  calc
    {target with locals := source.locals} = {source with clock := target.clock} := lifted
    _ = {source with clock := source.clock - 1} := by rw [targetClock]

/-- Actual escaping exceptions have the same exact read-only clock/frame
contract, with caller locals cleared by the real call semantics. -/
theorem exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (function : MlS) (arguments : List (ExpHOL 64))
    (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL)
    (code : source.code.lookup function = some (formals, body, shape))
    (pureBody : LocalEffects.Preserves source.code body) (quiet : QuietClock.Preserves source.code body)
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.call (some (none, none)) function arguments) = (some (.exception identifier payload), post)) :
    1 ≤ source.clock ∧ post.clock = source.clock - 1 ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - 1} := by
  obtain ⟨positive, values, actual, callee, returnShape, target, args, called, bodyRun, postEq, fields⟩ :=
    CallNormal.ignored_exception_data source post function arguments identifier payload run
  have identified := LocalEffects.lookup_body source.code function formals body shape code values actual callee returnShape called
  rw [identified] at bodyRun
  have frame := pureBody (callEntryStateHOLFinite source callee) rfl
  rw [bodyRun] at frame
  change LocalEffects.erase target = LocalEffects.erase source at frame
  have targetClock := quiet (callEntryStateHOLFinite source callee) rfl
  rw [bodyRun] at targetClock
  change target.clock = source.clock - 1 at targetClock
  have lifted := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with clock := target.clock}) frame
  refine ⟨positive, ?_, ?_⟩
  · rw [postEq]; exact targetClock
  · rw [postEq]
    change emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - 1}
    rw [← targetClock]
    exact lifted

end InitECandidate.Solver.Input.QuietReadOnlyCall

#print axioms InitECandidate.Solver.Input.QuietReadOnlyCall.normal
#print axioms InitECandidate.Solver.Input.QuietReadOnlyCall.exception
