import InitECandidate.Solver.Rlp.ValidationWrapperFrame
import InitECandidate.Solver.Rlp.ValidationCall

namespace InitECandidate.Solver.Rlp.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A real normal ignored caller retains all words above its saved scratch
cursor, restores caller locals/arena, and derives its actual caller cost. -/
theorem ignored_normal_outside (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_validate_items") arguments)=(none,post)) :
    1≤source.clock ∧ post.locals=source.locals ∧ Validation.Arena post cursor limit ∧ Validation.Outside source post limit.toNat cursor.toNat ∧
      source.clock-post.clock≤14*(2*length.toNat+1)+5 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_validate_items") body .one pointer length (original_code source.code installed)
  obtain ⟨positive,target,value,bodyRun⟩ := Input.CallNormal.ignored_callee_return source post (ofString "rlp_validate_items") arguments _ body callee .one args called normal
  obtain ⟨valueEq,nextArena,above⟩ := body_normal_outside (callEntryStateHOLFinite source callee) target pointer length cursor limit pointerLocal lengthLocal
    (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed value bodyRun
  rw [valueEq] at bodyRun
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "rlp_validate_items") arguments (Header.values pointer length) body callee .one
    (.val (.word 0#64)) target args called (by omega) bodyRun (by simp [shapeOfHOLExact,shapeEqHOL])
  have same : post={target with locals:=source.locals} := (Prod.mk.inj (normal.symm.trans actual)).2
  have price := call_cost source pointer length cursor limit (some none) arguments args arena fits installed
  change source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_validate_items") arguments)).2.clock≤_ at price
  rw [normal] at price
  refine ⟨positive,by rw [same],Validation.Arena.of_fields target post cursor limit nextArena ?_ ?_,?_,price⟩
  · rw [same]
  · rw [same]
  · intro query upper
    rw [same]
    exact above query upper


theorem ignored_normal_above (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_validate_items") arguments)=(none,post)) :
    1≤source.clock ∧ post.locals=source.locals ∧ Validation.Arena post cursor limit ∧ Validation.Above source post cursor.toNat ∧
      source.clock-post.clock≤14*(2*length.toNat+1)+5 := by
  obtain ⟨funded,locals,arena',outside,price⟩ := ignored_normal_outside source post pointer length cursor limit arguments args arena fits installed normal
  exact ⟨funded,locals,arena',fun query beyond=>outside query (Or.inr beyond),price⟩

end InitECandidate.Solver.Rlp.Validate

#print axioms InitECandidate.Solver.Rlp.Validate.ignored_normal_outside

#print axioms InitECandidate.Solver.Rlp.Validate.ignored_normal_above
