import InitECandidate.Solver.Input.BinaryCallData
import InitECandidate.Solver.Input.ScopedCallException
import InitECandidate.Solver.Input.PricedReadOnlyPrefix

namespace InitECandidate.Solver.Input.KnownBinaryPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (declaredShape : ShapeHOL)
    (function leftName rightName : MlS) (leftShape rightShape returnShape : ShapeHOL) (body : ProgHOL 64) (price : Nat)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (left right expected : ValueHOL 64) (identifier : MlS) (payload : ValueHOL 64)
    (distinct : leftName ≠ rightName)
    (code : source.code.lookup function = some ([(leftName, leftShape), (rightName, rightShape)], body, returnShape))
    (pureBody : LocalEffects.Preserves source.code body) (priced : ClockCost.Bound source.code body price)
    (read : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [left, right])
    (determines : ∀ (entry target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64), entry.code = source.code →
      LocalEffects.erase entry = LocalEffects.erase source →
      entry.locals.lookup leftName = some left → entry.locals.lookup rightName = some right →
      evaluateHOLFiniteState entry body = (some (.returned value), target) → value = expected)
    (safe : NoException.Safe source.code body)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) declaredShape function arguments continuation) = (some (.exception identifier payload), post)) :
    ∃ (paid : Nat) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      1 ≤ paid ∧ paid ≤ price + 1 ∧ paid ≤ source.clock ∧
      ready = setVarHOLFinite (ofString name) expected {source with clock := source.clock - paid} ∧
      LocalEffects.erase ready = LocalEffects.erase source ∧
      evaluateHOLFiniteState ready continuation = (some (.exception identifier payload), inner) ∧ post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, shape, target, args, called, cases⟩ :=
    CallNormal.scoped_exception_data source post name declaredShape function arguments continuation identifier payload run
  have bodyEq := LocalEffects.lookup_body source.code function [(leftName, leftShape), (rightName, rightShape)] body returnShape code values actual callee shape called
  rcases cases with escaped | continued
  · obtain ⟨bodyRun, postEq⟩ := escaped
    rw [bodyEq] at bodyRun
    have excluded := safe (callEntryStateHOLFinite source callee) rfl identifier payload
    rw [bodyRun] at excluded
    exact (excluded rfl).elim
  · obtain ⟨value, inner, bodyRun, checked, tailRun, postEq⟩ := continued
    have valuesEq := Option.some.inj (args.symm.trans read)
    rw [valuesEq] at called
    obtain ⟨bodyEq, shapeEq, leftCell, rightCell⟩ := CallNormal.binary_lookup_known source.code.lookup function leftName rightName leftShape rightShape body returnShape
      left right actual callee shape distinct code called
    have actualRun := bodyRun
    rw [bodyEq] at actualRun
    have valueEq := determines (callEntryStateHOLFinite source callee) target value rfl rfl leftCell rightCell actualRun
    obtain ⟨paid, nonzero, bound, fits, next⟩ := PricedReadOnlyPrefix.resume source target name function [(leftName, leftShape), (rightName, rightShape)] body returnShape price
      code pureBody priced positive values actual callee shape (by rw [valuesEq]; exact called) value bodyRun
    let ready := setVarHOLFinite (ofString name) expected {source with clock := source.clock - paid}
    refine ⟨paid, ready, inner, nonzero, bound, fits, rfl, rfl, ?_, postEq⟩
    rw [next, valueEq] at tailRun
    exact tailRun

end InitECandidate.Solver.Input.KnownBinaryPrefix

#print axioms InitECandidate.Solver.Input.KnownBinaryPrefix.exception
