import InitECandidate.Solver.Input.PricedReadOnlyPrefix
import InitECandidate.Solver.Input.UnaryCallData

namespace InitECandidate.Solver.Input.KnownUnaryPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Compose a proved value function with its genuine scoped call. The
returned continuation state is opaque to callers, with an exact equality
and nonlocal frame available for transporting current physical models. -/
theorem exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (declaredShape : ShapeHOL)
    (function formal : MlS) (argumentShape returnShape : ShapeHOL) (body : ProgHOL 64) (price : Nat)
    (expression : ExpHOL 64) (continuation : ProgHOL 64) (argument expected : ValueHOL 64) (identifier : MlS) (payload : ValueHOL 64)
    (code : source.code.lookup function = some ([(formal, argumentShape)], body, returnShape))
    (pureBody : LocalEffects.Preserves source.code body) (priced : ClockCost.Bound source.code body price)
    (read : eval source expression = some argument)
    (determines : ∀ (entry target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64), entry.code = source.code → entry.locals.lookup formal = some argument →
      evaluateHOLFiniteState entry body = (some (.returned value), target) → value = expected)
    (safe : NoException.Safe source.code body)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) declaredShape function [expression] continuation) = (some (.exception identifier payload), post)) :
    ∃ (paid : Nat) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      1 ≤ paid ∧ paid ≤ price + 1 ∧ paid ≤ source.clock ∧
      ready = setVarHOLFinite (ofString name) expected {source with clock := source.clock - paid} ∧
      LocalEffects.erase ready = LocalEffects.erase source ∧
      evaluateHOLFiniteState ready continuation = (some (.exception identifier payload), inner) ∧ post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, shape, target, args, called, cases⟩ :=
    CallNormal.scoped_exception_data source post name declaredShape function [expression] continuation identifier payload run
  have bodyEq := LocalEffects.lookup_body source.code function [(formal, argumentShape)] body returnShape code values actual callee shape called
  rcases cases with escaped | continued
  · obtain ⟨bodyRun, postEq⟩ := escaped
    rw [bodyEq] at bodyRun
    have excluded := safe (callEntryStateHOLFinite source callee) rfl identifier payload
    rw [bodyRun] at excluded
    exact (excluded rfl).elim
  · obtain ⟨value, inner, bodyRun, checked, tailRun, postEq⟩ := continued
    have expectedArgs : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [expression] = some [argument] := by
      simp only [eval] at read
      simp only [evalListHOLFinite, evalListHOLExact, read]
    have actualValues := Option.some.inj (args.symm.trans expectedArgs)
    rw [actualValues] at called
    obtain ⟨actualArgument, valuesEq, bodyEq, shapeEq, typed, binding⟩ :=
      CallNormal.unary_lookup_data source.code.lookup function formal argumentShape body returnShape code [argument] actual callee shape called
    have argumentEq : actualArgument = argument := (List.cons.inj valuesEq).1.symm
    rw [argumentEq] at binding
    have actualRun := bodyRun
    rw [bodyEq] at actualRun
    have valueEq := determines (callEntryStateHOLFinite source callee) target value rfl binding actualRun
    obtain ⟨paid, nonzero, bound, fits, next⟩ := PricedReadOnlyPrefix.resume source target name function [(formal, argumentShape)] body returnShape price
      code pureBody priced positive [argument] actual callee shape called value bodyRun
    let ready := setVarHOLFinite (ofString name) expected {source with clock := source.clock - paid}
    refine ⟨paid, ready, inner, nonzero, bound, fits, rfl, rfl, ?_, postEq⟩
    rw [next, valueEq] at tailRun
    exact tailRun

end InitECandidate.Solver.Input.KnownUnaryPrefix

#print axioms InitECandidate.Solver.Input.KnownUnaryPrefix.exception
