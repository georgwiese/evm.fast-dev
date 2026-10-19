import InitECandidate.Solver.Input.PricedReadOnlyPrefix
import InitECandidate.Solver.Input.RlpWrite.U256Shape

namespace InitECandidate.Solver.Input.PricedScalarPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (function : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL) (price : Nat)
    (code : source.code.lookup function = some (formals, body, returnShape))
    (pureBody : LocalEffects.Preserves source.code body) (priced : ClockCost.Bound source.code body price)
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one function arguments continuation) = (some (.returned returned), post)) :
    ∃ (paid : Nat) (word : BitVec 64) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      1 ≤ paid ∧ paid ≤ price + 1 ∧ paid ≤ source.clock ∧
      ready = setVarHOLFinite (ofString name) (.val (.word word)) {source with clock := source.clock - paid} ∧
      LocalEffects.erase ready = LocalEffects.erase source ∧
      evaluateHOLFiniteState ready continuation = (some (.returned returned), inner) ∧ post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, shape, target, value, inner, args, called, bodyRun, checked, tailRun, postEq⟩ :=
    CallNormal.scoped_data source post name .one function arguments continuation returned run
  have typed : shapeOfHOLExact value = .one := (shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1
  obtain ⟨word, valueEq⟩ := RlpWrite.U256Value.scalar_word value typed
  subst value
  obtain ⟨paid, nonzero, bound, fits, next⟩ := PricedReadOnlyPrefix.resume source target name function formals body returnShape price
    code pureBody priced positive values actual callee shape called (.val (.word word)) bodyRun
  let ready := setVarHOLFinite (ofString name) (.val (.word word)) {source with clock := source.clock - paid}
  refine ⟨paid, word, ready, inner, nonzero, bound, fits, rfl, rfl, ?_, postEq⟩
  rw [next] at tailRun
  exact tailRun

end InitECandidate.Solver.Input.PricedScalarPrefix

#print axioms InitECandidate.Solver.Input.PricedScalarPrefix.normal
