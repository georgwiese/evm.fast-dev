import InitECandidate.Solver.Rlp.ValidationCaughtNormal
import InitECandidate.Solver.Rlp.ValidationBodyFrame

namespace InitECandidate.Solver.Rlp.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem caught_normal_outside (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source caught=(none,target)) :
    target.locals=source.locals ∧ ∃ nextCursor,Validation.Arena target nextCursor limit ∧ nextCursor.toNat≤cursor.toNat ∧ Validation.Outside source target limit.toNat cursor.toNat := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "_rlp_validate_items_body") Validation.body .one pointer length (Validation.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length) := by
    simp [arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,WitnessRadix.QueryBranch.localVar,toExact,pointerCell,lengthCell]
  obtain ⟨positive,calleePost,value,bodyRun,checked,restored⟩ := Input.CallNormal.ignored_caught_stops source target (ofString "_rlp_validate_items_body") arguments _ Validation.body callee .one
    (ofString "RlpErr") (ofString "e") handler args called handler_stops normal
  obtain ⟨valueEq,nextCursor,nextArena,bounded,above⟩ := Validation.body_normal_outside (callEntryStateHOLFinite source callee) calleePost pointer length cursor limit pointerLocal lengthLocal
    (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed value bodyRun
  refine ⟨by rw [restored],nextCursor,Validation.Arena.of_fields calleePost target nextCursor limit nextArena ?_ ?_,bounded,?_⟩
  · rw [restored]
  · rw [restored]
  · intro query upper
    rw [restored]
    exact above query upper

end InitECandidate.Solver.Rlp.Validate

#print axioms InitECandidate.Solver.Rlp.Validate.caught_normal_outside
