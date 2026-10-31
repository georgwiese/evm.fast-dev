import InitECandidate.Solver.Mpt.CurrentWitnessStepCaught
import InitECandidate.Solver.Input.DeclarationTrace
import InitECandidate.Solver.Input.ScopeClock

namespace InitECandidate.Solver.Mpt.CurrentWitnessStep
open WitnessStep Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def zeroItem : ValueHOL 64 := .rStruct [.val (.word 0#64),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)]
def tupleEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) := setVarHOLFinite (ofString "it") zeroItem source
def parseEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) := QueryBranch.bind (tupleEntry source) "e" 0#64

theorem parse_entry_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (notItem : ofString "it"≠ofString name) (notError : ofString "e"≠ofString name) :
    (parseEntry source).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  rw [parseEntry,bind_lookup_other _ "e" name 0#64 notError]
  simp [tupleEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notItem]

/-- The current actual decode/resolve prefix derives its parsed tuple,
complete physical frame and real suffix execution. Error, malformed-input,
handler and short-clock outcomes remain bounded by the same source prefix. -/
theorem parsed_suffix_trace (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (body kind)=(outcome,post)) :
    source.clock-post.clock≤60*length.toNat+14 ∨ ∃ ready inner answer,
      parsed kind pointer length answer ∧ CurrentStartup.ArenaState ready ∧ Rlp.CurrentItem.Frame source ready ∧
      ready.locals.lookup (ofString "it")=some answer ∧ ready.locals.lookup (ofString "db")=some (.val (.word db)) ∧
      ready.locals.lookup (ofString "p")=some (.val (.word pointer)) ∧ ready.locals.lookup (ofString "n")=some (.val (.word length)) ∧
      ready.clock≤source.clock ∧ source.clock-ready.clock≤60*length.toNat+13 ∧
      evaluateHOLFiniteState ready (afterRlp kind)=(outcome,inner) ∧
      post=restore source "it" (restore (tupleEntry source) "e" inner) := by
  rw [body_shape] at run
  rcases declaration_trace source post "it" Rlp.Item.resultShape (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64])
      (.dec (ofString "e") .one (.const 0#64) (.seq (caught kind) (afterRlp kind))) outcome run with stopped|entered
  · exact Or.inl (by omega)
  · obtain ⟨declared,innerTuple,read,checked,tupleRun,postTuple⟩:=entered
    have zeroRead : eval source (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64])=some zeroItem := rfl
    have declaredEq : declared=zeroItem:=Option.some.inj (read.symm.trans zeroRead)
    subst declared
    obtain ⟨inner,enteredRun,postInner⟩:=ScalarScope.declare_trace (tupleEntry source) innerTuple "e" (.const 0#64) 0#64
      (.seq (caught kind) (afterRlp kind)) outcome rfl tupleRun
    change evaluateHOLFiniteState (parseEntry source) (.seq (caught kind) (afterRlp kind))=(outcome,inner) at enteredRun
    have currentDb:=(parse_entry_other source "db" (by decide) (by decide)).trans dbCell
    have currentPointer:=(parse_entry_other source "p" (by decide) (by decide)).trans pointerCell
    have currentLength:=(parse_entry_other source "n" (by decide) (by decide)).trans lengthCell
    have currentArena : CurrentStartup.ArenaState (parseEntry source):=arena.of_frame rfl
    have priced:=caught_cost kind (parseEntry source) pointer length currentPointer currentLength currentArena fits
    have postClock : post.clock=inner.clock := by rw [postTuple,postInner]; rfl
    rw [evaluateHOLFiniteState_seq_line780] at enteredRun
    generalize computed : evaluateHOLFiniteState (parseEntry source) (caught kind)=output at enteredRun
    obtain ⟨firstResult,current⟩:=output
    cases firstResult with
    | some result=>
      have endpoint : current=inner:=congrArg Prod.snd enteredRun
      rw [computed] at priced
      change source.clock-current.clock≤60*length.toNat+14 at priced
      exact Or.inl (by rw [postClock,←endpoint]; exact priced)
    | none=>
      obtain ⟨calleePost,answer,parsed,frame,forward,price,currentEq⟩:=caught_none kind (parseEntry source) current pointer length
        currentPointer currentLength currentArena fits computed
      have currentClock : current.clock=calleePost.clock := by rw [currentEq]; rfl
      have retained : Rlp.CurrentItem.Frame source current := frame.of_erase rfl rfl
      refine Or.inr ⟨current,inner,answer,parsed,arena.of_metadata retained.metadata,retained,?_,?_,?_,?_,?_,?_,enteredRun,?_⟩
      · rw [currentEq]; exact CallNormal.continuation_lookup_same _ _ _ _
      · rw [currentEq]; exact (CallNormal.continuation_lookup_other (parseEntry source) calleePost "it" "db" answer (by decide)).trans currentDb
      · rw [currentEq]; exact (CallNormal.continuation_lookup_other (parseEntry source) calleePost "it" "p" answer (by decide)).trans currentPointer
      · rw [currentEq]; exact (CallNormal.continuation_lookup_other (parseEntry source) calleePost "it" "n" answer (by decide)).trans currentLength
      · rw [currentClock]; exact forward
      · rw [currentClock]; exact price
      · rw [postTuple,postInner]

end InitECandidate.Solver.Mpt.CurrentWitnessStep

#print axioms InitECandidate.Solver.Mpt.CurrentWitnessStep.parsed_suffix_trace
