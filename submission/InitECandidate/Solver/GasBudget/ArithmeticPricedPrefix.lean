import InitECandidate.Solver.GasBudget.ArithmeticEffectsScoped
import InitECandidate.Solver.GasBudget.ArithmeticClockPrice

namespace InitECandidate.Solver.GasBudget.ArithmeticEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open Input.LocalEffects

/-- A real normal scoped arithmetic call reaches its actual continuation
with a checked value, unchanged nonlocal state and an actual lower clock.
Its spent clocks are bounded by the checked original body price plus1. -/
theorem priced_scoped_prefix (kind : Kind) (price : Nat) (checked : kind.fixedPrice = some price)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (environment : Environment source.code)
    (name : String) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) shape kind.name arguments continuation) = (some (.returned value), post)) :
    1 ≤ source.clock ∧ ∃ clock returned inner,
      clock < source.clock ∧ source.clock - clock ≤ price + 1 ∧ shapeEqHOL (shapeOfHOLExact returned) shape = true ∧
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) returned {source with clock := clock}) continuation = (some (.returned value), inner) ∧
      post = WitnessRadix.QueryBranch.restore source name inner := by
  obtain ⟨positive, values, actual, callee, returnShape, target, returned, inner, args, called, bodyRun, shapeChecked, continuationRun, postEq⟩ :=
    Input.CallNormal.scoped_data source post name shape kind.name arguments continuation value normal
  have bodyEq := lookup_body source.code kind.name kind.signature.1 kind.body kind.signature.2.2 (environment kind) values actual callee returnShape called
  rw [bodyEq] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  have frame := execution_frame kind entry target environment (some (.returned returned)) bodyRun
  change erase target = erase source at frame
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory =>
    {state with locals := source.locals, clock := target.clock}) frame
  have nextEq : Input.CallNormal.continuationEntry source target name returned =
      setVarHOLFinite (ofString name) returned {source with clock := target.clock} :=
    congrArg (setVarHOLFinite (ofString name) returned) callerFrame
  rw [nextEq] at continuationRun
  have bodyCost := fixed_clock_spent kind price checked entry target environment (some (.returned returned)) bodyRun
  change source.clock - 1 - target.clock ≤ price at bodyCost
  have targetClock := evaluateHOLFiniteState_clock_le entry kind.body
  rw [bodyRun] at targetClock
  change target.clock ≤ source.clock - 1 at targetClock
  exact ⟨positive, target.clock, returned, inner, by omega, by omega, (Bool.and_eq_true_iff.mp shapeChecked).1, continuationRun, postEq⟩

end InitECandidate.Solver.GasBudget.ArithmeticEffects

#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.priced_scoped_prefix
