import InitECandidate.Solver.Mpt.WitnessStepPrefixTrace
import InitECandidate.Solver.Input.NormalDeclarationEntry
import InitECandidate.Solver.Input.NoReturnCaught
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Mpt.WitnessStep
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine complete step return passes the caught parser normally.
The parser's actual value, arena and current suffix are derived, rather
than inferred from the stopping-or-continuation cost trace. -/
theorem parsed_suffix_normal (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length cursor limit : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (body kind)=(some (.returned value),post)) :
    ∃ ready inner answer,parsed kind pointer length answer ∧ Rlp.Validation.Arena ready cursor limit ∧
      Rlp.Validation.Above source ready cursor.toNat ∧ ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧ ready.code=source.code ∧
      (∀ key,ready.globals.lookup key=source.globals.lookup key) ∧
      ready.locals.lookup (ofString "it")=some answer ∧
      ready.locals.lookup (ofString "db")=some (.val (.word db)) ∧
      ready.locals.lookup (ofString "p")=some (.val (.word pointer)) ∧ ready.locals.lookup (ofString "n")=some (.val (.word length)) ∧
      ready.clock≤source.clock ∧ source.clock-ready.clock≤60*length.toNat+44 ∧
      evaluateHOLFiniteState ready (afterRlp kind)=(some (.returned value),inner) ∧
      post=restore source "it" (restore (tupleEntry source) "e" inner) := by
  rw [body_shape] at normal
  obtain ⟨declared,innerTuple,read,checked,tupleRun,postTuple⟩:=Input.CallNormal.declaration_normal_entry source post "it" Rlp.Item.resultShape
    (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64]) (.dec (ofString "e") .one (.const 0#64) (.seq (caught kind) (afterRlp kind))) value normal
  have zeroRead : eval source (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64])=some zeroItem:=rfl
  have declaredEq : declared=zeroItem:=Option.some.inj (read.symm.trans zeroRead)
  subst declared
  obtain ⟨inner,enteredRun,postInner⟩:=Input.ScalarScope.declare_trace (tupleEntry source) innerTuple "e" (.const 0#64) 0#64
    (.seq (caught kind) (afterRlp kind)) (some (.returned value)) rfl tupleRun
  change evaluateHOLFiniteState (parseEntry source) (.seq (caught kind) (afterRlp kind))=(some (.returned value),inner) at enteredRun
  have handlerNever : Input.NoReturn.Never handler:=Input.NoReturn.ignored_call (ofString "mpt_fail") [.const 3#64]
  have caughtNever : Input.NoReturn.Never (caught kind):=
    Input.NoReturn.caught_destination (some (.local,ofString "it")) (ofString (rlpName kind)) arguments (ofString "RlpErr") (ofString "e") handler handlerNever
  obtain ⟨current,parsedRun,continued⟩:=Input.sequence_returned (parseEntry source) inner (caught kind) (afterRlp kind) value
    (caughtNever (parseEntry source)) enteredRun
  have currentPointer:=(parse_entry_other source "p" (by decide) (by decide)).trans pointerCell
  have currentLength:=(parse_entry_other source "n" (by decide) (by decide)).trans lengthCell
  have currentDb:=(parse_entry_other source "db" (by decide) (by decide)).trans dbCell
  have currentArena:=Rlp.Validation.Arena.of_fields source (parseEntry source) cursor limit arena rfl rfl
  obtain ⟨funded,calleePost,answer,parsed,nextArena,above,domain,endian,codeEq,heapEq,globals,price,currentEq⟩:=
    caught_none kind (parseEntry source) current pointer length cursor limit currentPointer currentLength currentArena fits installed parsedRun
  have forward:=evaluateHOLFiniteState_clock_le (parseEntry source) (caught kind)
  rw [parsedRun] at forward
  change current.clock≤source.clock at forward
  have currentClock : current.clock=calleePost.clock:=by rw [currentEq]; rfl
  change source.clock-calleePost.clock≤60*length.toNat+44 at price
  refine ⟨current,inner,answer,parsed,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,forward,by rw [currentClock]; exact price,continued,?_⟩
  · rw [currentEq]
    exact Rlp.Validation.Arena.of_fields calleePost _ cursor limit nextArena rfl rfl
  · rw [currentEq]; exact above
  · rw [currentEq]; exact domain
  · rw [currentEq]; exact endian
  · rw [currentEq]; exact codeEq
  · rw [currentEq]; exact globals
  · rw [currentEq]; exact Input.CallNormal.continuation_lookup_same _ _ _ _
  · rw [currentEq]
    exact (Input.CallNormal.continuation_lookup_other (parseEntry source) calleePost "it" "db" answer (by decide)).trans currentDb
  · rw [currentEq]
    exact (Input.CallNormal.continuation_lookup_other (parseEntry source) calleePost "it" "p" answer (by decide)).trans currentPointer
  · rw [currentEq]
    exact (Input.CallNormal.continuation_lookup_other (parseEntry source) calleePost "it" "n" answer (by decide)).trans currentLength
  · rw [postTuple,postInner]

end InitECandidate.Solver.Mpt.WitnessStep

#print axioms InitECandidate.Solver.Mpt.WitnessStep.parsed_suffix_normal
