import InitECandidate.Solver.GasBudget.U256FromBePrice
import InitECandidate.Solver.Input.BinaryCallData
import InitECandidate.Solver.Input.ScopedCallData
import InitECandidate.Solver.Input.RlpWrite.U256Shape

namespace InitECandidate.Solver.GasBudget.U256FromBe
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite

theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "u256_from_be") = some ([(ofString "p", .one), (ofString "n", .one)], body, U256Value.tupleShape) := by
  simpa only [ArithmeticEffects.Kind.name, ArithmeticEffects.Kind.signature, ArithmeticEffects.Kind.original,
    Guest.guestFn_u256_from_be, body, ArithmeticEffects.Kind.body, paramToHOL, shapeToHOL, U256Value.tupleShape,
    List.map_cons, List.map_nil] using OriginalCodeEnvironment.arithmetic code installed .u256_from_be

set_option maxHeartbeats 1000000 in
theorem normal_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : Input.OriginalCode.Installed source.code) (pointer : BitVec 64) (length : Nat) (small : length < 2 ^ 64)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (value : ValueHOL 64)
    (read : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some [.val (.word pointer), .val (.word (BitVec.ofNat 64 length))])
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) U256Value.tupleShape (ofString "u256_from_be") arguments continuation) = (some (.returned value), post)) :
    ∃ (paid : Nat) (words : U256Value.Words) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      1 ≤ paid ∧ paid ≤ max 4 length + 1 ∧ paid ≤ source.clock ∧
      ready = setVarHOLFinite (ofString name) (U256Value.tuple words) {source with clock := source.clock - paid} ∧
      Input.LocalEffects.erase ready = Input.LocalEffects.erase source ∧
      evaluateHOLFiniteState ready continuation = (some (.returned value), inner) ∧ post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, shape, target, returned, inner, args, called, bodyRun, checked, tailRun, postEq⟩ :=
    Input.CallNormal.scoped_data source post name U256Value.tupleShape (ofString "u256_from_be") arguments continuation value normal
  have valuesEq := Option.some.inj (args.symm.trans read)
  rw [valuesEq] at called
  obtain ⟨bodyEq, shapeEq, pointerCell, lengthCell⟩ := Input.CallNormal.binary_lookup_known source.code.lookup (ofString "u256_from_be")
    (ofString "p") (ofString "n") .one .one body U256Value.tupleShape (.val (.word pointer)) (.val (.word (BitVec.ofNat 64 length)))
    actual callee shape (by decide) (original_code source.code installed) called
  rw [bodyEq] at bodyRun
  have typed : shapeOfHOLExact returned = U256Value.tupleShape := (shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1
  obtain ⟨words, returnedEq⟩ := U256Value.of_shape returned typed
  subst returned
  let entry := callEntryStateHOLFinite source callee
  change evaluateHOLFiniteState entry body = (some (.returned (U256Value.tuple words)), target) at bodyRun
  have effect := ArithmeticEffects.pure_u256_from_be source.code (OriginalCodeEnvironment.arithmetic source.code installed) entry rfl
  change Input.LocalEffects.erase (evaluateHOLFiniteState entry body).2 = Input.LocalEffects.erase entry at effect
  rw [bodyRun] at effect
  change Input.LocalEffects.erase target = Input.LocalEffects.erase source at effect
  have cost := body_price entry installed length small lengthCell
  rw [bodyRun] at cost
  change source.clock - 1 - target.clock ≤ max 4 length at cost
  have clock := evaluateHOLFiniteState_clock_le entry body
  rw [bodyRun] at clock
  change target.clock ≤ source.clock - 1 at clock
  let paid := source.clock - target.clock
  have actualClock : target.clock = source.clock - paid := by dsimp only [paid]; omega
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals, clock := target.clock}) effect
  have next := congrArg (setVarHOLFinite (ofString name) (U256Value.tuple words)) callerFrame
  change Input.CallNormal.continuationEntry source target name (U256Value.tuple words) = setVarHOLFinite (ofString name) (U256Value.tuple words) {source with clock := target.clock} at next
  rw [actualClock] at next
  let ready := setVarHOLFinite (ofString name) (U256Value.tuple words) {source with clock := source.clock - paid}
  refine ⟨paid, words, ready, inner, by dsimp only [paid]; omega, by dsimp only [paid]; omega,
    by dsimp only [paid]; omega, rfl, rfl, ?_, postEq⟩
  rw [next] at tailRun
  exact tailRun

end InitECandidate.Solver.GasBudget.U256FromBe

#print axioms InitECandidate.Solver.GasBudget.U256FromBe.original_code
#print axioms InitECandidate.Solver.GasBudget.U256FromBe.normal_prefix
