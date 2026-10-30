import InitECandidate.Solver.Rlp.ValidationCost
import InitECandidate.Solver.Rlp.ValidationLoopFrame
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real normal internal-validator return retains every ordinary word
above its incoming scratch cursor, and derives cursor monotonicity. -/
theorem body_normal_outside (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    value=.val (.word 0#64) ∧ ∃ nextCursor,Arena target nextCursor limit ∧ nextCursor.toNat≤cursor.toNat ∧ Outside source target limit.toNat cursor.toNat := by
  rw [body_shape] at normal
  obtain ⟨topInner,topRun,topRestore⟩ := Input.declaration_return_word source target "top" (.const 0#64) 0#64 _ value rfl normal
  let topState := bind source "top" 0#64
  have pointerRead : eval topState (localVar "p")=some (.val (.word pointer)) := by
    have current := (bind_lookup_other source "top" "p" 0#64 (by decide)).trans pointerCell
    change topState.locals.lookup (ofString "p")=_ at current
    simp [eval,evalHOLExact,localVar,toExact,current]
  obtain ⟨positionInner,positionRun,positionRestore⟩ := Input.declaration_return_word topState topInner "pos" _ pointer _ value pointerRead topRun
  let positionState := bind topState "pos" pointer
  have currentPointer : positionState.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
    (bind_lookup_other _ "pos" "p" _ (by decide)).trans ((bind_lookup_other _ "top" "p" _ (by decide)).trans pointerCell)
  have currentLength : positionState.locals.lookup (ofString "len")=some (.val (.word length)) :=
    (bind_lookup_other _ "pos" "len" _ (by decide)).trans ((bind_lookup_other _ "top" "len" _ (by decide)).trans lengthCell)
  have endRead : eval positionState (.op .add [localVar "p",localVar "len"])=some (.val (.word (pointer+length))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,currentPointer,currentLength,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨endInner,endRun,endRestore⟩ := Input.declaration_return_word positionState positionInner "end" _ (pointer+length) _ value endRead positionRun
  let endState := bind positionState "end" (pointer+length)
  obtain ⟨goInner,goRun,goRestore⟩ := Input.declaration_return_word endState endInner "go" (.const 1#64) 1#64 _ value rfl endRun
  let goState := bind endState "go" 1#64
  have noReturns : ∀ returned,(evaluateHOLFiniteState goState loop).1≠some (.returned returned) := by
    rw [loop_shape]
    exact ((Input.LocalPrefix.loop condition loop_body_prefix).summary_full goState).2.1
  obtain ⟨middle,loopRun,returnRun⟩ := Input.sequence_returned goState goInner loop (.return (.const 0#64)) value noReturns goRun
  have view : View goState (pointer+length) cursor limit pointer (pointer+length) 1#64 [] := seeded_view source pointer length cursor limit arena fits
  obtain ⟨nextCursor,nextArena,bounded,above⟩ := loop_none_outside goState middle (pointer+length) cursor limit pointer (pointer+length) 1#64 [] view installed loopRun
  obtain ⟨read,returned⟩ := Input.return_normal middle goInner (.const 0#64) value returnRun
  have valueEq : value=.val (.word 0#64) := (Option.some.inj read).symm
  refine ⟨valueEq,nextCursor,Arena.of_fields middle target nextCursor limit nextArena ?_ ?_,bounded,?_⟩
  · rw [topRestore,positionRestore,endRestore,goRestore,returned]
    rfl
  · rw [topRestore,positionRestore,endRestore,goRestore,returned]
    rfl
  · intro query upper
    rw [topRestore,positionRestore,endRestore,goRestore,returned]
    exact above query upper


theorem body_normal_above (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    value=.val (.word 0#64) ∧ ∃ nextCursor,Arena target nextCursor limit ∧ nextCursor.toNat≤cursor.toNat ∧ Above source target cursor.toNat := by
  obtain ⟨returned,next,arena',decreases,outside⟩ := body_normal_outside source target pointer length cursor limit pointerCell lengthCell arena fits installed value normal
  exact ⟨returned,next,arena',decreases,fun query beyond=>outside query (Or.inr beyond)⟩

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.body_normal_outside

#print axioms InitECandidate.Solver.Rlp.Validation.body_normal_above
