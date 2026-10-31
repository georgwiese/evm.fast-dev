import InitECandidate.Solver.Mpt.CurrentWitnessStepPrefix
import InitECandidate.Solver.Input.NormalDeclarationEntry
import InitECandidate.Solver.Input.NoReturnCaught
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Mpt.CurrentWitnessStep
open WitnessStep Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- A real normal enclosing return must pass the actual caught parser.
Its successful suffix is derived from the same execution. -/
theorem parsed_suffix_normal (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.LiveArena source) (fits : pointer.toNat+length.toNat<2^64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (body kind)=(some (.returned value),post)) :
    ∃ ready inner answer,parsed kind pointer length answer ∧ Rlp.LiveArena ready ∧
      Rlp.CurrentItem.Frame source ready ∧
      (∀ cursor limit,Rlp.Validation.Arena source cursor limit→Rlp.Validation.Above source ready cursor.toNat) ∧
      ready.locals.lookup (ofString "it")=some answer ∧ ready.locals.lookup (ofString "db")=some (.val (.word db)) ∧
      ready.locals.lookup (ofString "p")=some (.val (.word pointer)) ∧ ready.locals.lookup (ofString "n")=some (.val (.word length)) ∧
      ready.clock≤source.clock ∧ source.clock-ready.clock≤60*length.toNat+13 ∧
      evaluateHOLFiniteState ready (afterRlp kind)=(some (.returned value),inner) ∧
      post=restore source "it" (restore (tupleEntry source) "e" inner) := by
  rw [body_shape] at normal
  obtain ⟨declared,innerTuple,read,checked,tupleRun,postTuple⟩:=CallNormal.declaration_normal_entry source post "it" Rlp.Item.resultShape
    (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64])
    (.dec (ofString "e") .one (.const 0#64) (.seq (caught kind) (afterRlp kind))) value normal
  have zeroRead : eval source (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64])=some zeroItem:=rfl
  have declaredEq : declared=zeroItem:=Option.some.inj (read.symm.trans zeroRead)
  subst declared
  obtain ⟨inner,enteredRun,postInner⟩:=ScalarScope.declare_trace (tupleEntry source) innerTuple "e" (.const 0#64) 0#64
    (.seq (caught kind) (afterRlp kind)) (some (.returned value)) rfl tupleRun
  change evaluateHOLFiniteState (parseEntry source) (.seq (caught kind) (afterRlp kind))=(some (.returned value),inner) at enteredRun
  have handlerNever : NoReturn.Never handler:=NoReturn.ignored_call (ofString "mpt_fail") [.const 3#64]
  have caughtNever : NoReturn.Never (caught kind):=
    NoReturn.caught_destination (some (.local,ofString "it")) (ofString (rlpName kind)) arguments (ofString "RlpErr") (ofString "e") handler handlerNever
  obtain ⟨current,parsedRun,continued⟩:=sequence_returned (parseEntry source) inner (caught kind) (afterRlp kind) value
    (caughtNever (parseEntry source)) enteredRun
  have currentPointer:=(parse_entry_other source "p" (by decide) (by decide)).trans pointerCell
  have currentLength:=(parse_entry_other source "n" (by decide) (by decide)).trans lengthCell
  have currentDb:=(parse_entry_other source "db" (by decide) (by decide)).trans dbCell
  have currentArena : Rlp.LiveArena (parseEntry source):=arena.of_frame rfl
  obtain ⟨calleePost,answer,parsed,frame,above,forward,price,currentEq⟩:=caught_none kind (parseEntry source) current pointer length
    currentPointer currentLength currentArena fits parsedRun
  have retained : Rlp.CurrentItem.Frame source current:=frame.of_erase rfl rfl
  have retainedAbove : ∀ cursor limit,Rlp.Validation.Arena source cursor limit→Rlp.Validation.Above source current cursor.toNat:=by
    intro cursor limit physical
    exact above cursor limit (physical.of_fields source (parseEntry source) cursor limit rfl rfl)
  have currentClock : current.clock=calleePost.clock:=by rw [currentEq]; rfl
  refine ⟨current,inner,answer,parsed,arena.of_metadata retained.metadata,retained,retainedAbove,?_,?_,?_,?_,?_,?_,continued,?_⟩
  · rw [currentEq]; exact CallNormal.continuation_lookup_same _ _ _ _
  · rw [currentEq]; exact (CallNormal.continuation_lookup_other (parseEntry source) calleePost "it" "db" answer (by decide)).trans currentDb
  · rw [currentEq]; exact (CallNormal.continuation_lookup_other (parseEntry source) calleePost "it" "p" answer (by decide)).trans currentPointer
  · rw [currentEq]; exact (CallNormal.continuation_lookup_other (parseEntry source) calleePost "it" "n" answer (by decide)).trans currentLength
  · rw [currentClock]; exact forward
  · rw [currentClock]; exact price
  · rw [postTuple,postInner]

end InitECandidate.Solver.Mpt.CurrentWitnessStep

#print axioms InitECandidate.Solver.Mpt.CurrentWitnessStep.parsed_suffix_normal
