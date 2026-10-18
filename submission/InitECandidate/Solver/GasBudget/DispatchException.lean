import InitECandidate.Solver.GasBudget.DispatchSelection
import InitECandidate.Solver.Input.IgnoredCallException

namespace InitECandidate.Solver.GasBudget.OpcodeDispatch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- An actual dispatcher exception is the original invalid-opcode raise or
an exception from the selected original opcode helper. Partial opcode work
before failure therefore remains visible to the global accounting proof. -/
theorem exception_helper (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (op : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word op)))
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception identifier payload), post)) :
    (evaluateHOLFiniteState source (.raise (ofString "EvmErr") (.const 5#64)) = (some (.exception identifier payload), post)) ∨
      (∃ function arguments, tree.choose op = .invoke function arguments ∧
        evaluateHOLFiniteState source (.call (some (none, none)) (ofString function) arguments) = (some (.exception identifier payload), post)) := by
  rcases evaluation_cases source op opLocal with invalid | ⟨function, arguments, selected, execution⟩
  · left
    rw [← invalid]
    exact run
  · right
    refine ⟨function, arguments, selected, ?_⟩
    rw [execution, evaluateHOLFiniteState_seq_line780] at run
    generalize computed : evaluateHOLFiniteState source (.call (some (none, none)) (ofString function) arguments) = output at run ⊢
    obtain ⟨result, target⟩ := output
    cases result with
    | none =>
      change evaluateHOLFiniteState target (.return (.const 0#64)) = (some (.exception identifier payload), post) at run
      have actualReturn : evaluateHOLFiniteState target (.return (.const 0#64)) =
          (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite target) := by
        simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact]
      rw [actualReturn] at run
      cases run
    | some result => exact run

theorem exception_callee (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (op : BitVec 64)
    (opLocal : source.locals.lookup (ofString "op") = some (.val (.word op)))
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source body = (some (.exception identifier payload), post)) :
    (evaluateHOLFiniteState source (.raise (ofString "EvmErr") (.const 5#64)) = (some (.exception identifier payload), post)) ∨
      (1 ≤ source.clock ∧ ∃ function arguments values calleeBody callee returnShape target,
        tree.choose op = .invoke function arguments ∧
        evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values ∧
        lookupCodeHOLFinite source.code.lookup (ofString function) values = some (calleeBody, callee, returnShape) ∧
        evaluateHOLFiniteState (callEntryStateHOLFinite source callee) calleeBody = (some (.exception identifier payload), target) ∧
        post = emptyLocalsHOLFinite target ∧ target.memaddrs = source.memaddrs ∧ target.be = source.be ∧
        target.eshapes = source.eshapes ∧ target.code = source.code) := by
  rcases exception_helper source post op opLocal identifier payload run with invalid | ⟨function, arguments, selected, called⟩
  · exact Or.inl invalid
  · obtain ⟨positive, values, calleeBody, callee, returnShape, target, args, lookup, bodyRun, frame, fields⟩ :=
      Input.CallNormal.ignored_exception_data source post (ofString function) arguments identifier payload called
    exact Or.inr ⟨positive, function, arguments, values, calleeBody, callee, returnShape, target, selected, args, lookup, bodyRun, frame, fields⟩

end InitECandidate.Solver.GasBudget.OpcodeDispatch

#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.exception_helper
#print axioms InitECandidate.Solver.GasBudget.OpcodeDispatch.exception_callee
