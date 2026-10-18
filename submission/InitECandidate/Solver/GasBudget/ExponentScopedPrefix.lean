import InitECandidate.Solver.GasBudget.ExponentAllPrice
import InitECandidate.Solver.GasBudget.ArithmeticEffectsScoped
import InitECandidate.Solver.Input.ScopedCallData

namespace InitECandidate.Solver.GasBudget.Exponent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine successful original exponentiation declaration reaches its
actual continuation with only locals/clock changed and<=4867paid clocks.
Neither callee execution nor caller funding is an input premise. -/
theorem normal_scoped (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : ArithmeticEffects.Environment source.code) (name : String) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) shape (ofString "u256_exp") arguments continuation) = (some (.returned value), post)) :
    ∃ paid ready inner, paid ≤ 4867 ∧ paid ≤ source.clock ∧ ready.clock = source.clock - paid ∧
      emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with clock := source.clock - paid} ∧
      evaluateHOLFiniteState ready continuation = (some (.returned value), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  obtain ⟨positive, values, actual, callee, returnShape, target, returned, inner, args, called, bodyRun, checked, tailRun, postEq⟩ :=
    Input.CallNormal.scoped_data source post name shape (ofString "u256_exp") arguments continuation value normal
  have bodyEq := Input.LocalEffects.lookup_body source.code (ofString "u256_exp")
    ArithmeticEffects.Kind.u256_exp.signature.1 ArithmeticEffects.Kind.u256_exp.body ArithmeticEffects.Kind.u256_exp.signature.2.2
    (environment .u256_exp) values actual callee returnShape called
  rw [bodyEq] at bodyRun
  let entry := callEntryStateHOLFinite source callee
  have fields := ArithmeticEffects.execution_frame .u256_exp entry target environment (some (.returned returned)) bodyRun
  change Input.LocalEffects.erase target = Input.LocalEffects.erase source at fields
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals, clock := target.clock}) fields
  have nextEq : Input.CallNormal.continuationEntry source target name returned = setVarHOLFinite (ofString name) returned {source with clock := target.clock} :=
    congrArg (setVarHOLFinite (ofString name) returned) callerFrame
  rw [nextEq] at tailRun
  have cost := full_body_price source.code environment entry rfl
  rw [bodyRun] at cost
  change source.clock - 1 - target.clock ≤ 4866 at cost
  have clock := evaluateHOLFiniteState_clock_le entry ArithmeticEffects.Kind.u256_exp.body
  rw [bodyRun] at clock
  change target.clock ≤ source.clock - 1 at clock
  let paid := source.clock - target.clock
  let ready := setVarHOLFinite (ofString name) returned {source with clock := target.clock}
  have actualClock : target.clock = source.clock - paid := by dsimp only [paid]; omega
  refine ⟨paid, ready, inner, by dsimp only [paid]; omega, by dsimp only [paid]; omega, actualClock, ?_, tailRun, ?_⟩
  · change emptyLocalsHOLFinite {source with clock := target.clock} = emptyLocalsHOLFinite {source with clock := source.clock - paid}
    rw [actualClock]
  · rw [postEq]
    rfl

end InitECandidate.Solver.GasBudget.Exponent

#print axioms InitECandidate.Solver.GasBudget.Exponent.normal_scoped
