import InitECandidate.Solver.Rlp.CurrentValidation.Cost
import InitECandidate.Solver.Input.LoopInvariant
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Rlp.CurrentValidation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- Every actual continuing loop prefix is pure outside locals/clock. The
failed nested push is never identified with a normal continuing state. -/
theorem loop_none_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (position ending go : BitVec 64)
    (data : State source position ending go) (normal : evaluateHOLFiniteState source Validation.loop=(none,post)) :
    LocalEffects.erase post=LocalEffects.erase source := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>Invariant ending current ∧ LocalEffects.erase current=LocalEffects.erase source
  have initial : invariant source := ⟨⟨position,go,data⟩,rfl⟩
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code → invariant current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) Validation.condition=some (.val (.word word)) →
      word≠0 → current.clock≠0 → ∀ target,evaluateHOLFiniteState (decClockHOLFinite current) Validation.loopBody=(none,target) → invariant target := by
    intro current codeEq model word read nonzero funded target actual
    obtain ⟨position,go,data⟩ := model.1
    have active:=data.condition_active word read nonzero
    subst go
    obtain ⟨next,nextGo,nextData,smaller,frame⟩ := loop_body_none (decClockHOLFinite current) target position ending (data.at_clock (current.clock-1)) actual
    exact ⟨⟨next,nextGo,nextData⟩,frame.trans model.2⟩
  rw [Validation.loop_shape] at normal
  exact (loop_invariant source.code (ofString "p") Validation.condition Validation.loopBody Validation.loop_body_prefix invariant progress source post rfl initial normal).2

/-- The whole current internal validator returns zero and preserves all
nonlocal state on any actual normal return, including its real declarations,
loop and lexical restoration. Actual nested scratch stores cannot reach here. -/
theorem body_normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source Validation.body=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ LocalEffects.erase post=LocalEffects.erase source := by
  rw [Validation.body_shape] at normal
  obtain ⟨topInner,topRun,topRestore⟩ := declaration_return_word source post "top" (.const 0#64) 0#64 _ value rfl normal
  let topState:=bind source "top" 0#64
  have pointerRead : eval topState (localVar "p")=some (.val (.word pointer)) := by
    have cell:=(bind_lookup_other source "top" "p" 0#64 (by decide)).trans pointerCell
    change topState.locals.lookup (ofString "p")=_ at cell
    simp [eval,evalHOLExact,localVar,toExact,cell]
  obtain ⟨positionInner,positionRun,positionRestore⟩ := declaration_return_word topState topInner "pos" (localVar "p") pointer _ value pointerRead topRun
  let positionState:=bind topState "pos" pointer
  have currentPointer : positionState.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
    (bind_lookup_other topState "pos" "p" pointer (by decide)).trans ((bind_lookup_other source "top" "p" 0#64 (by decide)).trans pointerCell)
  have currentLength : positionState.locals.lookup (ofString "len")=some (.val (.word length)) :=
    (bind_lookup_other topState "pos" "len" pointer (by decide)).trans ((bind_lookup_other source "top" "len" 0#64 (by decide)).trans lengthCell)
  have endRead : eval positionState (.op .add [localVar "p",localVar "len"])=some (.val (.word (pointer+length))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,currentPointer,currentLength,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨endInner,endRun,endRestore⟩ := declaration_return_word positionState positionInner "end" _ (pointer+length) _ value endRead positionRun
  let endState:=bind positionState "end" (pointer+length)
  obtain ⟨goInner,goRun,goRestore⟩ := declaration_return_word endState endInner "go" (.const 1#64) 1#64 _ value rfl endRun
  let goState:=bind endState "go" 1#64
  have noReturns : ∀ returned,(evaluateHOLFiniteState goState Validation.loop).1≠some (.returned returned) := by
    rw [Validation.loop_shape]
    exact ((LocalPrefix.loop Validation.condition Validation.loop_body_prefix).summary_full goState).2.1
  obtain ⟨middle,loopRun,returnRun⟩ := sequence_returned goState goInner Validation.loop (.return (.const 0#64)) value noReturns goRun
  have frame:=loop_none_frame goState middle pointer (pointer+length) 1#64 (seeded_state source pointer length arena fits) loopRun
  obtain ⟨read,returned⟩ := return_normal middle goInner (.const 0#64) value returnRun
  have valueEq : value=.val (.word 0#64) := by
    have canonical : eval middle (.const 0#64)=some (.val (.word 0#64)) := rfl
    exact Option.some.inj (read.symm.trans canonical)
  refine ⟨valueEq,?_⟩
  rw [topRestore,positionRestore,endRestore,goRestore,returned]
  exact frame

end InitECandidate.Solver.Rlp.CurrentValidation

#print axioms InitECandidate.Solver.Rlp.CurrentValidation.loop_none_frame
#print axioms InitECandidate.Solver.Rlp.CurrentValidation.body_normal_frame
