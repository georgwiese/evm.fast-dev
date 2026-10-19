import InitECandidate.Solver.Rlp.ValidationWrapper
import InitECandidate.Solver.Rlp.ValidationNormal
import InitECandidate.Solver.Input.CaughtCallStops
import InitECandidate.Solver.Input.NoReturnCaught
import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.Input.PureGuardNormal

namespace InitECandidate.Solver.Rlp.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem handler_stops : Input.NoFallthrough handler :=
  Input.NoFallthrough.sequence release _ (fun current=>Input.raise_ne_none current _ _)

theorem handler_no_return : Input.NoReturn.Never handler :=
  Input.NoReturn.sequence release _ (Input.NoReturn.ignored_call _ _) (Input.NoReturn.raise _ _)

theorem caught_no_return : Input.NoReturn.Never caught :=
  Input.NoReturn.caught_call _ _ _ _ _ handler_no_return

theorem caught_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source caught=(none,target)) :
    target.locals=source.locals ∧ ∃ nextCursor,Validation.Arena target nextCursor limit := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "_rlp_validate_items_body") Validation.body .one pointer length (Validation.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length) := by
    simp [arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,WitnessRadix.QueryBranch.localVar,toExact,pointerCell,lengthCell]
  obtain ⟨positive,calleePost,value,bodyRun,checked,restored⟩ := Input.CallNormal.ignored_caught_stops source target (ofString "_rlp_validate_items_body") arguments _ Validation.body callee .one
    (ofString "RlpErr") (ofString "e") handler args called handler_stops normal
  obtain ⟨valueEq,nextCursor,nextArena⟩ := Validation.body_normal (callEntryStateHOLFinite source callee) calleePost pointer length cursor limit pointerLocal lengthLocal
    (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed value bodyRun
  refine ⟨by rw [restored],nextCursor,Validation.Arena.of_fields calleePost target nextCursor limit nextArena ?_ ?_⟩
  · rw [restored]
  · rw [restored]

end InitECandidate.Solver.Rlp.Validate

#print axioms InitECandidate.Solver.Rlp.Validate.handler_stops
#print axioms InitECandidate.Solver.Rlp.Validate.handler_no_return
#print axioms InitECandidate.Solver.Rlp.Validate.caught_no_return
#print axioms InitECandidate.Solver.Rlp.Validate.caught_normal
