import InitECandidate.Solver.Input.RlpWrite.LengthNormal
import InitECandidate.Solver.Input.RlpWrite.U256Lookup
import InitECandidate.Solver.Input.ScopedCallData
import InitECandidate.Solver.Input.ScopedCallException

namespace InitECandidate.Solver.GasBudget.ByteLengthCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.RlpWrite

theorem resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (code : source.code.lookup (ofString "u256_byte_length") = some (U256ByteLength.formals, U256ByteLength.body, .one))
    (bitsCode : source.code.lookup (ofString "u256_bit_length") = some (U256Bits.formals, U256Bits.body, .one))
    (bitCode : source.code.lookup (ofString "bit_length64") = some (BitLength.formals, BitLength.body, .one))
    (values : List (ValueHOL 64)) (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "u256_byte_length") values = some (actual, callee, returnShape))
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actual = (some (.returned returned), target)) :
    ∃ bytes, bytes ≤ 32 ∧ 3 ≤ source.clock ∧ returned = .val (.word (BitVec.ofNat 64 bytes)) ∧
      Input.CallNormal.continuationEntry source target name returned = bind {source with clock := source.clock - 3} name (BitVec.ofNat 64 bytes) := by
  obtain ⟨words, valuesEq, bodyEq, shapeEq, a⟩ := U256Value.unary_lookup source.code.lookup _ U256ByteLength.body code values actual callee returnShape called
  rw [bodyEq] at run
  obtain ⟨bytes, small, returnedEq, fits, clock, frame⟩ :=
    U256ByteLength.normal (callEntryStateHOLFinite source callee) target words a bitsCode bitCode returned run
  change 2 ≤ source.clock - 1 at fits
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) frame
  change {target with locals := source.locals} = {source with clock := source.clock - 1 - 2} at callerFrame
  have next := congrArg (setVarHOLFinite (ofString name) returned) callerFrame
  refine ⟨bytes, small, by omega, returnedEq, ?_⟩
  simpa only [Input.CallNormal.continuationEntry, WitnessRadix.QueryBranch.bind, returnedEq, Nat.sub_sub,
    show 1 + 2 = 3 from rfl] using next

theorem no_callee_exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words)
    (a : source.locals.lookup (ofString "a") = some (U256Value.tuple words))
    (bitsCode : source.code.lookup (ofString "u256_bit_length") = some (U256Bits.formals, U256Bits.body, .one))
    (bitCode : source.code.lookup (ofString "bit_length64") = some (BitLength.formals, BitLength.body, .one))
    (identifier : MlS) (payload : ValueHOL 64)
    (run : evaluateHOLFiniteState source U256ByteLength.body = (some (.exception identifier payload), post)) : False := by
  have shifted := panPropsEvaluateAddClockEq U256ByteLength.body source (some (.exception identifier payload)) post 2
    ⟨run, by intro impossible; cases impossible⟩
  obtain ⟨target, bytes, small, actual, frame⟩ := U256ByteLength.execute {source with clock := source.clock + 2}
    words a bitsCode bitCode (by change 2 ≤ source.clock + 2; omega)
  have impossible := congrArg Prod.fst (shifted.symm.trans actual)
  cases impossible

/-- Actual normal scoped byte-length call: arguments, original lookup,
callee value, <=32 result and all three paid clocks are derived. -/
theorem normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (code : source.code.lookup (ofString "u256_byte_length") = some (U256ByteLength.formals, U256ByteLength.body, .one))
    (bitsCode : source.code.lookup (ofString "u256_bit_length") = some (U256Bits.formals, U256Bits.body, .one))
    (bitCode : source.code.lookup (ofString "bit_length64") = some (BitLength.formals, BitLength.body, .one))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source
      (.decCall (ofString name) .one (ofString "u256_byte_length") arguments continuation) = (some (.returned value), post)) :
    ∃ bytes inner, bytes ≤ 32 ∧ 3 ≤ source.clock ∧
      evaluateHOLFiniteState (bind {source with clock := source.clock - 3} name (BitVec.ofNat 64 bytes)) continuation = (some (.returned value), inner) ∧
      post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, returnShape, target, returned, inner, args, called, bodyRun, checked, tailRun, postEq⟩ :=
    Input.CallNormal.scoped_data source post name .one _ arguments continuation value run
  obtain ⟨bytes, small, fits, returnedEq, next⟩ := resume source target name code bitsCode bitCode values actual callee returnShape called returned bodyRun
  exact ⟨bytes, inner, small, fits, by rw [← next]; exact tailRun, postEq⟩

/-- A real escaping exception can only come from the actual continuation
after the same checked byte-length result; the helper itself cannot throw. -/
theorem exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (code : source.code.lookup (ofString "u256_byte_length") = some (U256ByteLength.formals, U256ByteLength.body, .one))
    (bitsCode : source.code.lookup (ofString "u256_bit_length") = some (U256Bits.formals, U256Bits.body, .one))
    (bitCode : source.code.lookup (ofString "bit_length64") = some (BitLength.formals, BitLength.body, .one))
    (identifier : MlS) (payload : ValueHOL 64) (run : evaluateHOLFiniteState source
      (.decCall (ofString name) .one (ofString "u256_byte_length") arguments continuation) = (some (.exception identifier payload), post)) :
    ∃ bytes inner, bytes ≤ 32 ∧ 3 ≤ source.clock ∧
      evaluateHOLFiniteState (bind {source with clock := source.clock - 3} name (BitVec.ofNat 64 bytes)) continuation = (some (.exception identifier payload), inner) ∧
      post = restore source name inner := by
  obtain ⟨positive, values, actual, callee, returnShape, target, args, called, cases⟩ :=
    Input.CallNormal.scoped_exception_data source post name .one _ arguments continuation identifier payload run
  rcases cases with escaped | continued
  · obtain ⟨bodyRun, postEq⟩ := escaped
    obtain ⟨words, valuesEq, bodyEq, shapeEq, a⟩ := U256Value.unary_lookup source.code.lookup _ U256ByteLength.body code values actual callee returnShape called
    rw [bodyEq] at bodyRun
    exact (no_callee_exception (callEntryStateHOLFinite source callee) target words a bitsCode bitCode identifier payload bodyRun).elim
  · obtain ⟨returned, inner, bodyRun, checked, tailRun, postEq⟩ := continued
    obtain ⟨bytes, small, fits, returnedEq, next⟩ := resume source target name code bitsCode bitCode values actual callee returnShape called returned bodyRun
    exact ⟨bytes, inner, small, fits, by rw [← next]; exact tailRun, postEq⟩

end InitECandidate.Solver.GasBudget.ByteLengthCall

#print axioms InitECandidate.Solver.GasBudget.ByteLengthCall.resume
#print axioms InitECandidate.Solver.GasBudget.ByteLengthCall.no_callee_exception
#print axioms InitECandidate.Solver.GasBudget.ByteLengthCall.normal
#print axioms InitECandidate.Solver.GasBudget.ByteLengthCall.exception
