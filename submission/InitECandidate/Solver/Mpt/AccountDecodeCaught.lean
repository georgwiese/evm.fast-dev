import InitECandidate.Solver.Mpt.AccountDecodeProgram
import InitECandidate.Solver.Rlp.DecodeNormalFrame
import InitECandidate.Solver.Rlp.DecodeGlobals
import InitECandidate.Solver.Input.CaughtAssignedStops
import InitECandidate.Solver.Input.ClockCostCaughtAssigned
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem caught_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) decodeArguments=some (Rlp.Header.values pointer length) := by
  simp [decodeArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]

theorem caught_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) : source.clock-(evaluateHOLFiniteState source caught).2.clock≤60*length.toNat+45 := by
  have args := caught_arguments source pointer length pointerCell lengthCell
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_decode_fully") Rlp.Decode.body Rlp.Item.resultShape pointer length
    (Rlp.Decode.original_code source.code installed)
  have firstCost := Rlp.Decode.body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal
    (Rlp.Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed
  have handlerCost : Input.ClockCost.Bound source.code handler 1 := Fail.call_price source.code installed [.const 20#64]
  rw [caught]
  have priced := Input.ClockCost.caught_destination_current source (some (.local,ofString "it")) (ofString "rlp_decode_fully") decodeArguments _ Rlp.Decode.body callee Rlp.Item.resultShape
    (ofString "RlpErr") (ofString "e") handler (60*length.toNat+43) 1 args called firstCost handlerCost
  omega

/-- A genuine normal caught decode recovers its actual complete item and
readonly-input/scratch frame. A caught RlpErr cannot pass the original MPT
failure handler; no exception-shape or successful future decode is assumed. -/
theorem caught_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (normal : evaluateHOLFiniteState source caught=(none,target)) :
    1≤source.clock ∧ ∃ calleePost answer,
      Rlp.Decode.Complete pointer length answer ∧ Rlp.Validation.Arena calleePost cursor limit ∧
      Rlp.Validation.Above source calleePost cursor.toNat ∧ calleePost.memaddrs=source.memaddrs ∧ calleePost.be=source.be ∧
      calleePost.code=source.code ∧ calleePost.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") ∧
      source.clock-calleePost.clock≤60*length.toNat+44 ∧ target=Input.CallNormal.continuationEntry source calleePost "it" answer := by
  have args := caught_arguments source pointer length pointerCell lengthCell
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_decode_fully") Rlp.Decode.body Rlp.Item.resultShape pointer length
    (Rlp.Decode.original_code source.code installed)
  have stops : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → (evaluateHOLFiniteState current handler).1≠none := by
    intro current codeEq passed
    have currentInstalled : Input.OriginalCode.Installed current.code := by rw [codeEq]; exact installed
    exact Fail.call_not_normal current _ currentInstalled [.const 20#64] (Prod.ext passed rfl)
  obtain ⟨positive,calleePost,answer,bodyRun,checked,targetEq⟩ := Input.CallNormal.assigned_caught_stops source target (ofString "it") (ofString "rlp_decode_fully") decodeArguments _ Rlp.Decode.body callee Rlp.Item.resultShape
    (ofString "RlpErr") (ofString "e") handler args called stops normal
  obtain ⟨complete,nextArena,above,price⟩ := Rlp.Decode.body_normal_above (callEntryStateHOLFinite source callee) calleePost pointer length cursor limit pointerLocal lengthLocal
    (Rlp.Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed answer bodyRun
  have fields := Input.evaluation_fields (callEntryStateHOLFinite source callee) calleePost Rlp.Decode.body (some (.returned answer)) bodyRun
  have heapFrame := Rlp.Decode.globals (ofString "heap_ptr") source.code installed (by decide) (callEntryStateHOLFinite source callee) rfl
  rw [bodyRun] at heapFrame
  have heapEq := congrArg Prod.snd heapFrame
  have clock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) Rlp.Decode.body
  rw [bodyRun] at clock
  change calleePost.clock≤source.clock-1 at clock
  change source.clock-1-calleePost.clock≤60*length.toNat+43 at price
  exact ⟨positive,calleePost,answer,complete,nextArena,above,fields.1,fields.2.1,fields.2.2.2,heapEq,by omega,targetEq⟩

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.caught_arguments
#print axioms InitECandidate.Solver.Mpt.AccountDecode.caught_cost
#print axioms InitECandidate.Solver.Mpt.AccountDecode.caught_none
