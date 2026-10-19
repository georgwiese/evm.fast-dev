import InitECandidate.Solver.Rlp.ListCountCall
import InitECandidate.Solver.Rlp.ListCountNormalFrame

namespace InitECandidate.Solver.Rlp.ListCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem ignored_normal_above (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_list_count") arguments)=(none,post)) :
    post.locals=source.locals ∧ Validation.Arena post cursor limit ∧ Validation.Above source post cursor.toNat := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_count") body .one pointer length (original_code source.code installed)
  obtain ⟨positive,target,value,bodyRun⟩ := Input.CallNormal.ignored_callee_return source post (ofString "rlp_list_count") arguments _ body callee .one args called normal
  obtain ⟨countWord,valueEq,bounded,nextArena,above⟩ := body_normal_above (callEntryStateHOLFinite source callee) target pointer length cursor limit pointerLocal lengthLocal
    (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed value bodyRun
  rw [valueEq] at bodyRun
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "rlp_list_count") arguments (Header.values pointer length) body callee .one
    (.val (.word countWord)) target args called (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
  have same : post={target with locals:=source.locals} := (Prod.mk.inj (normal.symm.trans actual)).2
  refine ⟨by rw [same],Validation.Arena.of_fields target post cursor limit nextArena ?_ ?_,?_⟩
  · rw [same]
  · rw [same]
  · intro query upper
    rw [same]
    exact above query upper

end InitECandidate.Solver.Rlp.ListCount

#print axioms InitECandidate.Solver.Rlp.ListCount.ignored_normal_above
