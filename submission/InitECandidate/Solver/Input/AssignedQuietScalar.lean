import InitECandidate.Solver.Input.AssignedCallData
import InitECandidate.Solver.Input.UnaryCallData
import InitECandidate.Solver.Input.ClockCost
import InitECandidate.Solver.Input.LocalEffects
import InitECandidate.Solver.Input.RlpWrite.U256Shape

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem assigned_quiet_scalar (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name function formal : MlS)
    (arguments : List (ExpHOL 64)) (body : ProgHOL 64)
    (code : source.code.lookup function = some ([(formal, .one)], body, .one))
    (pureBody : LocalEffects.Preserves source.code body) (priced : ClockCost.Bound source.code body 0)
    (normal : evaluateHOLFiniteState source (.call (some (some (.local, name), none)) function arguments) = (none, post)) :
    1 ≤ source.clock ∧ ∃ word : BitVec 64, post = setVarHOLFinite name (.val (.word word)) {source with clock := source.clock - 1} := by
  obtain ⟨positive, values, actual, callee, shape, target, returned, args, called, bodyRun, checked, postEq⟩ := CallNormal.local_data source post name function arguments normal
  obtain ⟨argument, valuesEq, bodyEq, shapeEq, argumentShape, binding⟩ := CallNormal.unary_lookup_data source.code.lookup function formal .one body .one
    code values actual callee shape called
  rw [shapeEq] at checked
  have typed : shapeOfHOLExact returned = .one := (shapeEqHOL_eq_true _ _).mp checked
  obtain ⟨word, valueEq⟩ := RlpWrite.U256Value.scalar_word returned typed
  subst returned
  rw [bodyEq] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  have fields := pureBody entry rfl
  rw [bodyRun] at fields
  change LocalEffects.erase target = LocalEffects.erase source at fields
  have cost := priced entry rfl
  rw [bodyRun] at cost
  have clock := evaluateHOLFiniteState_clock_le entry body
  rw [bodyRun] at clock
  change source.clock - 1 - target.clock ≤ 0 at cost
  change target.clock ≤ source.clock - 1 at clock
  have targetClock : target.clock = source.clock - 1 := by omega
  have frame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals, clock := target.clock}) fields
  change {target with locals := source.locals} = {source with clock := target.clock} at frame
  refine ⟨positive, word, ?_⟩
  rw [postEq, frame, targetClock]

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.assigned_quiet_scalar
