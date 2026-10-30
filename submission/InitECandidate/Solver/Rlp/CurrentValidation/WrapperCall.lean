import InitECandidate.Solver.Rlp.CurrentValidation.WrapperMemory
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.Rlp.CurrentValidate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix

/-- The public validator's actual ABI adds one source caller tick to its
complete saved-mark/caught-release body allowance. All outcomes are included. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length)) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "rlp_validate_items") expressions)).2.clock≤14*(2*length.toNat+1)+5 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_validate_items") body .one pointer length (original_code source.code arena.code)
  have paid:=body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits
  exact ClockCost.call_current source destination (ofString "rlp_validate_items") expressions (Header.values pointer length) body callee .one
    (14*(2*length.toNat+1)+4) args called paid

/-- Actual normal ignored validator calls retain runtime metadata and
all memory outside their temporary scratch interval. -/
theorem ignored_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_validate_items") expressions)=(none,post)) :
    MemoryMetadata.erase post=MemoryMetadata.erase source ∧
      Validation.Outside source post 2952790016 2965299200 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_validate_items") body .one pointer length (original_code source.code arena.code)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (ofString "rlp_validate_items") expressions actual
  have valuesEq:=Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq:=Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have frame:=body_normal_frame (callEntryStateHOLFinite source callee) target pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits returned bodyRun
  rw [endpoint]
  exact ⟨frame.2.1, ⟨frame.2.2.runtime, fun query outside => frame.2.2 query outside⟩⟩

end InitECandidate.Solver.Rlp.CurrentValidate

#print axioms InitECandidate.Solver.Rlp.CurrentValidate.call_cost
#print axioms InitECandidate.Solver.Rlp.CurrentValidate.ignored_frame
