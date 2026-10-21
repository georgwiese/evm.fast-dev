import InitECandidate.Solver.Mpt.WitnessStepCaught
import InitECandidate.Solver.Input.DeclarationTrace
import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.Input.ScopeClock

namespace InitECandidate.Solver.Mpt.WitnessStep
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def zeroItem : ValueHOL 64 := .rStruct [.val (.word 0#64),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)]
def tupleEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) := setVarHOLFinite (ofString "it") zeroItem source
def parseEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) := QueryBranch.bind (tupleEntry source) "e" 0#64

theorem parse_entry_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String)
    (notItem : ofString "it"≠ofString name) (notError : ofString "e"≠ofString name) :
    (parseEntry source).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  rw [parseEntry,bind_lookup_other _ "e" name 0#64 notError]
  simp [tupleEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notItem]

/-- Every actual original decode/resolve body either stops within its
RLP-prefix allowance or reaches the real suffix with the genuinely parsed
item, restored scratch cursor, and protected memory above that cursor.
The original two local restorations and suffix execution are retained. -/
theorem parsed_suffix_trace (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length cursor limit : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (body kind)=(outcome,post)) :
    source.clock-post.clock≤60*length.toNat+45 ∨ ∃ ready inner answer,
      parsed kind pointer length answer ∧ Rlp.Validation.Arena ready cursor limit ∧
      Rlp.Validation.Above source ready cursor.toNat ∧ ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧ ready.code=source.code ∧
      ready.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") ∧
      (∀ key,ready.globals.lookup key=source.globals.lookup key) ∧
      ready.locals.lookup (ofString "it")=some answer ∧
      ready.locals.lookup (ofString "db")=some (.val (.word db)) ∧
      ready.locals.lookup (ofString "p")=some (.val (.word pointer)) ∧ ready.locals.lookup (ofString "n")=some (.val (.word length)) ∧
      ready.clock≤source.clock ∧ source.clock-ready.clock≤60*length.toNat+44 ∧
      evaluateHOLFiniteState ready (afterRlp kind)=(outcome,inner) ∧
      post=restore source "it" (restore (tupleEntry source) "e" inner) := by
  rw [body_shape] at run
  rcases Input.declaration_trace source post "it" Rlp.Item.resultShape (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64])
      (.dec (ofString "e") .one (.const 0#64) (.seq (caught kind) (afterRlp kind))) outcome run with stopped|entered
  · exact Or.inl (by omega)
  · obtain ⟨declared,innerTuple,read,checked,tupleRun,postTuple⟩:=entered
    have zeroRead : eval source (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64])=some zeroItem := rfl
    have declaredEq : declared=zeroItem:=Option.some.inj (read.symm.trans zeroRead)
    subst declared
    obtain ⟨inner,enteredRun,postInner⟩:=Input.ScalarScope.declare_trace (tupleEntry source) innerTuple "e" (.const 0#64) 0#64
      (.seq (caught kind) (afterRlp kind)) outcome rfl tupleRun
    change evaluateHOLFiniteState (parseEntry source) (.seq (caught kind) (afterRlp kind))=(outcome,inner) at enteredRun
    have currentDb:=(parse_entry_other source "db" (by decide) (by decide)).trans dbCell
    have currentPointer:=(parse_entry_other source "p" (by decide) (by decide)).trans pointerCell
    have currentLength:=(parse_entry_other source "n" (by decide) (by decide)).trans lengthCell
    have currentArena:=Rlp.Validation.Arena.of_fields source (parseEntry source) cursor limit arena rfl rfl
    have priced:=caught_cost kind (parseEntry source) pointer length cursor limit currentPointer currentLength currentArena fits installed
    have postClock : post.clock=inner.clock := by rw [postTuple,postInner]; rfl
    rw [evaluateHOLFiniteState_seq_line780] at enteredRun
    generalize computed : evaluateHOLFiniteState (parseEntry source) (caught kind)=output at enteredRun
    obtain ⟨firstResult,current⟩:=output
    cases firstResult with
    | some result=>
      have endpoint : current=inner:=congrArg Prod.snd enteredRun
      rw [computed] at priced
      change source.clock-current.clock≤60*length.toNat+45 at priced
      exact Or.inl (by rw [postClock,←endpoint]; exact priced)
    | none=>
      obtain ⟨positive,calleePost,answer,parsed,nextArena,above,domain,endian,codeEq,heapEq,globalCells,price,currentEq⟩:=
        caught_none kind (parseEntry source) current pointer length cursor limit currentPointer currentLength currentArena fits installed computed
      have forward:=evaluateHOLFiniteState_clock_le (parseEntry source) (caught kind)
      rw [computed] at forward
      change current.clock≤source.clock at forward
      have currentClock : current.clock=calleePost.clock := by rw [currentEq]; rfl
      change source.clock-calleePost.clock≤60*length.toNat+44 at price
      refine Or.inr ⟨current,inner,answer,parsed,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,forward,by rw [currentClock]; exact price,enteredRun,?_⟩
      · rw [currentEq]
        exact Rlp.Validation.Arena.of_fields calleePost _ cursor limit nextArena rfl rfl
      · rw [currentEq]; exact above
      · rw [currentEq]; exact domain
      · rw [currentEq]; exact endian
      · rw [currentEq]; exact codeEq
      · rw [currentEq]; exact heapEq
      · rw [currentEq]; exact globalCells
      · rw [currentEq]; exact Input.CallNormal.continuation_lookup_same _ _ _ _
      · rw [currentEq]
        exact (Input.CallNormal.continuation_lookup_other (parseEntry source) calleePost "it" "db" answer (by decide)).trans currentDb
      · rw [currentEq]
        exact (Input.CallNormal.continuation_lookup_other (parseEntry source) calleePost "it" "p" answer (by decide)).trans currentPointer
      · rw [currentEq]
        exact (Input.CallNormal.continuation_lookup_other (parseEntry source) calleePost "it" "n" answer (by decide)).trans currentLength
      · rw [postTuple,postInner]

end InitECandidate.Solver.Mpt.WitnessStep

#print axioms InitECandidate.Solver.Mpt.WitnessStep.parse_entry_other
#print axioms InitECandidate.Solver.Mpt.WitnessStep.parsed_suffix_trace
