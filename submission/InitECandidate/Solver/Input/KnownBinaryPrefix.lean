import InitECandidate.Solver.Input.BinaryCallData
import InitECandidate.Solver.Input.PricedReadOnlyPrefix

namespace InitECandidate.Solver.Input.KnownBinaryPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (declaredShape : ShapeHOL)
    (function leftName rightName : MlS) (leftShape rightShape returnShape : ShapeHOL) (body : ProgHOL 64) (price : Nat)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (left right expected returned : ValueHOL 64)
    (distinct : leftName ≠ rightName)
    (code : source.code.lookup function = some ([(leftName, leftShape), (rightName, rightShape)], body, returnShape))
    (pureBody : LocalEffects.Preserves source.code body) (priced : ClockCost.Bound source.code body price)
    (read : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [left, right])
    (determines : ∀ (entry target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64), entry.code = source.code →
      LocalEffects.erase entry = LocalEffects.erase source →
      entry.locals.lookup leftName = some left → entry.locals.lookup rightName = some right →
      evaluateHOLFiniteState entry body = (some (.returned value), target) → value = expected)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) declaredShape function arguments continuation) = (some (.returned returned), post)) :
    ∃ (paid : Nat) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      1 ≤ paid ∧ paid ≤ price + 1 ∧ paid ≤ source.clock ∧
      ready = setVarHOLFinite (ofString name) expected {source with clock := source.clock - paid} ∧
      LocalEffects.erase ready = LocalEffects.erase source ∧
      evaluateHOLFiniteState ready continuation = (some (.returned returned), inner) ∧ post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, shape, target, value, inner, args, called, bodyRun, checked, tailRun, postEq⟩ :=
    CallNormal.scoped_data source post name declaredShape function arguments continuation returned run
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

#print axioms InitECandidate.Solver.Input.KnownBinaryPrefix.normal
