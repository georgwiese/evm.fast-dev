import InitECandidate.Solver.GasBudget.DispatchSelection
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every actual normal dispatcher body ran its selected original opcode
helper normally and returned literal zero. Lookup/callee traces and call
funding below are derived, not supplied as entry assumptions. -/
theorem normal_helper (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (op : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word op)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ ∃ function arguments middle,
      tree.choose op = .invoke function arguments ∧
      evaluateHOLFiniteState source (.call (some (none, none)) (ofString function) arguments) = (none, middle) ∧
      post = emptyLocalsHOLFinite middle := by
  rcases evaluation_cases source op opLocal with invalid | ⟨function, arguments, selected, execution⟩
  · rw [invalid] at normal
    exact (Input.NoReturn.raise (ofString "EvmErr") (.const 5#64) source returned (congrArg Prod.fst normal)).elim
  · rw [execution] at normal
    have safe : Input.LocalPrefix (ofString "op") (.call (some (none, none)) (ofString function) arguments) :=
      .call none _ _ (by intro name impossible; cases impossible)
    obtain ⟨middle, helperRun, returnRun, saved⟩ := safe.normal_continue source post (.return (.const 0#64)) returned normal
    have actualReturn : evaluateHOLFiniteState middle (.return (.const 0#64)) =
        (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite middle) := by
      simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
    have returnedEq : returned = .val (.word 0#64) := by
      simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using congrArg Prod.fst (returnRun.symm.trans actualReturn)
    exact ⟨returnedEq, function, arguments, middle, selected, helperRun, congrArg Prod.snd (returnRun.symm.trans actualReturn)⟩

theorem normal_callee (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (op : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word op)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ 1 ≤ source.clock ∧
      ∃ function arguments values calleeBody callee returnShape target helperReturned,
        tree.choose op = .invoke function arguments ∧
        evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values ∧
        lookupCodeHOLFinite source.code.lookup (ofString function) values = some (calleeBody, callee, returnShape) ∧
        evaluateHOLFiniteState (callEntryStateHOLFinite source callee) calleeBody = (some (.returned helperReturned), target) ∧
        shapeEqHOL (shapeOfHOLExact helperReturned) returnShape = true ∧
        post = emptyLocalsHOLFinite target ∧ target.memaddrs = source.memaddrs ∧ target.be = source.be ∧
        target.eshapes = source.eshapes ∧ target.code = source.code := by
  obtain ⟨returnedEq, function, arguments, middle, selected, helperRun, postEq⟩ := normal_helper source post op opLocal returned normal
  obtain ⟨positive, values, calleeBody, callee, returnShape, target, helperReturned, args, called, bodyRun, shape, middleEq, fields⟩ :=
    Input.CallNormal.ignored_data source middle (ofString function) arguments helperRun
  refine ⟨returnedEq, positive, function, arguments, values, calleeBody, callee, returnShape, target, helperReturned,
    selected, args, called, bodyRun, shape, ?_, fields⟩
  rw [postEq, middleEq]
  rfl

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.normal_helper
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.normal_callee
