import InitECandidate.Solver.GasBudget.CallGasCall
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
import InitECandidate.Solver.Input.PureNormal
import InitECandidate.Solver.Input.ScopedCallData

namespace InitECandidate.Solver.GasBudget.CallGas
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "calculate_message_call_gas") = some (formals, body, returnShape) := by
  have checked := Input.OriginalCode.indexed code installed 556
    (OriginalCodeEnvironment.originalEntry Guest.guestFn_calculate_message_call_gas) (by rfl)
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, body, formals, returnShape,
    Guest.guestFn_calculate_message_call_gas, shapeToHOL, paramToHOL, Input.RlpWrite.U256Value.tupleShape, List.map_cons, List.map_nil] using checked

/-- Actual successful calculator execution supplies its own two clocks,
exact capped pair and unchanged nonlocal state; no funding premise. -/
theorem normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Zero.Quad) (requested left : BitVec 64)
    (inputs : Inputs source words requested left)
    (zeroCode : source.code.lookup (ofString "u256_is_zero") = some (U256Zero.formals, U256Zero.body, .one))
    (addCode : source.code.lookup (ofString "add_sat") = some (AddExact.formals, AddExact.body, .one))
    (actual : ValueHOL 64) (run : evaluateHOLFiniteState source body = (some (.returned actual), post)) :
    actual = pair (capped requested left) (capped requested left + stipend words) ∧ 2 ≤ source.clock ∧
      post.clock = source.clock - 2 ∧ emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - 2} := by
  apply Input.PureNormal.from_funded source post body 2 _ actual run
  intro entry locals code enough
  exact execute entry words requested left (Inputs.of_locals source entry words requested left locals inputs)
    (by rw [code]; exact zeroCode) (by rw [code]; exact addCode) enough

/-- Actual five-argument scoped call in the zero-memory/extra mode of the
four original CALL opcodes. The real pair, three paid clocks and continuation
are recovered from the reached call rather than supplied in advance. -/
theorem call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Zero.Quad) (requested left : BitVec 64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64) (returned : ValueHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some (values words requested left))
    (code : source.code.lookup (ofString "calculate_message_call_gas") = some (formals, body, returnShape))
    (zeroCode : source.code.lookup (ofString "u256_is_zero") = some (U256Zero.formals, U256Zero.body, .one))
    (addCode : source.code.lookup (ofString "add_sat") = some (AddExact.formals, AddExact.body, .one))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) returnShape (ofString "calculate_message_call_gas") expressions continuation) = (some (.returned returned), post)) :
    3 ≤ source.clock ∧ ∃ inner,
      evaluateHOLFiniteState (callerPost source name (capped requested left) (capped requested left + stipend words)) continuation = (some (.returned returned), inner) ∧
      post = restore source name inner := by
  obtain ⟨positive, actualValues, actualBody, callee, shape, target, result, inner, actualArgs, called, bodyRun, checked, tailRun, postEq⟩ :=
    Input.CallNormal.scoped_data source post name returnShape (ofString "calculate_message_call_gas") expressions continuation returned run
  have valuesEq := Option.some.inj (actualArgs.symm.trans args)
  rw [valuesEq] at called
  obtain ⟨known, expectedCall, inputs⟩ := environment source.code.lookup words requested left code
  have same := Option.some.inj (called.symm.trans expectedCall)
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl, rfl⟩ := same
  obtain ⟨valueEq, funded, clock, frame⟩ := normal_value (callEntryStateHOLFinite source callee) target words requested left
    (inputs _ rfl) zeroCode addCode result bodyRun
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
  change {target with locals := source.locals} = {source with clock := source.clock - 1 - 2} at callerFrame
  have subtraction : source.clock - 1 - 2 = source.clock - 3 := by omega
  rw [subtraction] at callerFrame
  have canonical : Input.CallNormal.continuationEntry source target name result =
      callerPost source name (capped requested left) (capped requested left + stipend words) := by
    rw [valueEq]
    exact congrArg (setVarHOLFinite (ofString name) (pair (capped requested left) (capped requested left + stipend words))) callerFrame
  change 2 ≤ source.clock - 1 at funded
  exact ⟨by omega, inner, by rw [canonical] at tailRun; exact tailRun, postEq⟩

end InitECandidate.Solver.GasBudget.CallGas

#print axioms InitECandidate.Solver.GasBudget.CallGas.original_code
#print axioms InitECandidate.Solver.GasBudget.CallGas.normal_value
#print axioms InitECandidate.Solver.GasBudget.CallGas.call_normal
