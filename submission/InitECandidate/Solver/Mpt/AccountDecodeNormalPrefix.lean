import InitECandidate.Solver.Mpt.AccountDecodeCaught
import InitECandidate.Solver.Input.NoReturnCaught
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.NormalDeclarationEntry
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def zeroItem : ValueHOL 64 := .rStruct [.val (.word 0#64),.val (.word 0#64),.val (.word 0#64),.val (.word 0#64)]
def tupleEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) := setVarHOLFinite (ofString "it") zeroItem source
def decodeEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) := bind (tupleEntry source) "e" 0#64

theorem caught_never_returns : Input.NoReturn.Never caught :=
  Input.NoReturn.caught_destination (some (.local,ofString "it")) (ofString "rlp_decode_fully") decodeArguments
    (ofString "RlpErr") (ofString "e") handler (Input.NoReturn.ignored_call (ofString "mpt_fail") [.const 20#64])

set_option maxRecDepth 10000 in
/-- A complete actual normal account decode has really initialized both
locals, completed its caught RLP call and reached the list-processing suffix.
The genuine complete item, entry heap/arena, memory frame and resumed run
are derived, including lexical restoration around the complete result. -/
theorem body_decode_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length cursor limit out : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (arena : Rlp.Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    ∃ answer ready inner,
      Rlp.Decode.Complete pointer length answer ∧ Rlp.Validation.Arena ready cursor limit ∧
      Rlp.Validation.Above source ready cursor.toNat ∧ ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧ ready.code=source.code ∧
      ready.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") ∧
      ready.locals.lookup (ofString "it")=some answer ∧ ready.locals.lookup (ofString "acct_out")=some (.val (.word out)) ∧
      evaluateHOLFiniteState ready afterDecode=(some (.returned returned),inner) ∧
      emptyLocalsHOLFinite post=emptyLocalsHOLFinite inner := by
  rw [body_shape] at normal
  obtain ⟨declared,innerTuple,read,shapePass,tupleRun,postTuple⟩ := Input.CallNormal.declaration_normal_entry source post "it" Rlp.Item.resultShape
    (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64]) _ returned normal
  have zeroRead : eval source (.rstruct [.const 0#64,.const 0#64,.const 0#64,.const 0#64])=some zeroItem := by
    simp [zeroItem,eval,evalHOLExact,evalListHOLExact]
  have declaredEq : declared=zeroItem := Option.some.inj (read.symm.trans zeroRead)
  subst declared
  obtain ⟨inner,enteredRun,postInner⟩ := Input.declaration_return_word (tupleEntry source) innerTuple "e" (.const 0#64) 0#64 _ returned rfl tupleRun
  have enteredOther (name : String) (notItem : ofString "it"≠ofString name) (notError : ofString "e"≠ofString name) :
      (decodeEntry source).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    rw [decodeEntry,bind_lookup_other _ "e" name 0#64 notError]
    simp [tupleEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,notItem]
  have currentPointer := (enteredOther "p" (by decide) (by decide)).trans pointerCell
  have currentLength := (enteredOther "n" (by decide) (by decide)).trans lengthCell
  have currentOutput := (enteredOther "acct_out" (by decide) (by decide)).trans outputCell
  have currentArena := Rlp.Validation.Arena.of_fields source (decodeEntry source) cursor limit arena rfl rfl
  obtain ⟨ready,caughtRun,tailRun⟩ := Input.sequence_returned (decodeEntry source) inner caught afterDecode returned
    (fun value=>caught_never_returns _ value) enteredRun
  obtain ⟨positive,calleePost,answer,complete,nextArena,above,domain,endian,codeEq,heapEq,price,readyEq⟩ :=
    caught_none (decodeEntry source) ready pointer length cursor limit currentPointer currentLength currentArena fits installed caughtRun
  refine ⟨answer,ready,inner,complete,?_,?_,?_,?_,?_,?_,?_,?_,tailRun,?_⟩
  · rw [readyEq]
    exact Rlp.Validation.Arena.of_fields calleePost _ cursor limit nextArena rfl rfl
  · rw [readyEq]
    exact above
  · rw [readyEq]; exact domain
  · rw [readyEq]; exact endian
  · rw [readyEq]; exact codeEq
  · rw [readyEq]; exact heapEq
  · rw [readyEq]
    exact Input.CallNormal.continuation_lookup_same _ _ _ _
  · rw [readyEq]
    exact (Input.CallNormal.continuation_lookup_other (decodeEntry source) calleePost "it" "acct_out" answer (by decide)).trans currentOutput
  · rw [postTuple,postInner]
    rfl

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.caught_never_returns
#print axioms InitECandidate.Solver.Mpt.AccountDecode.body_decode_prefix
