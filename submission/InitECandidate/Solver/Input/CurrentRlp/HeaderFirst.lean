import InitECandidate.Solver.Input.CurrentRlp.HeaderRest
import InitECandidate.Solver.Input.ScopedCallNormal
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.CurrentRlp.HeaderFirst
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch HeaderEncoding

/-- Install the real first writer result and perform the actual p update.
All premises here are observations of that same returned child, supplied
by the checked writer contract in the composing theorems below. -/
theorem advance_returned (source child : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory)
    (header buffer : BitVec 64) (encoded : Nat) (context : Context source original header buffer)
    (metadata : MemoryMetadata.erase child=MemoryMetadata.erase source) (memory : OldMemory child.memory original buffer)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer 9))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer))) :
    ∃ next,Context next original header buffer ∧ MemoryMetadata.erase next=MemoryMetadata.erase source ∧
      next.clock=child.clock ∧
      next.locals.lookup (ofString "p")=some (.val (.word (address buffer (9+encoded)))) ∧
      next.locals.lookup (ofString "buf")=some (.val (.word buffer)) ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source child "w" (.val (.word (BitVec.ofNat 64 encoded)))) advance=(none,next) := by
  let ready:=CallNormal.continuationEntry source child "w" (.val (.word (BitVec.ofNat 64 encoded)))
  have wReady : ready.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 encoded))):=CallNormal.continuation_lookup_same _ _ _ _
  have otherReady (name : String) (different : ofString "w"≠ofString name) : ready.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    CallNormal.continuation_lookup_other _ _ "w" name _ different
  have pReady:=(otherReady "p" (by decide)).trans p
  have read : eval ready advanceExpression=some (.val (.word (address buffer (9+encoded)))):=by
    simp [eval,advanceExpression,localVar,evalHOLExact,evalListHOLExact,toExact,pReady,wReady,valueIsWord,valueWord,wordOpHOL,wordOp,
      address,BitVec.ofNat_add,BitVec.add_assoc]
  let next:=bind ready "p" (address buffer (9+encoded))
  have otherNext (name : String) (different : ofString "p"≠ofString name) : next.locals.lookup (ofString name)=ready.locals.lookup (ofString name):=
    bind_lookup_other _ "p" name _ different
  have globals:=congrArg PanSemStateFiniteExact.globals metadata
  change child.globals=source.globals at globals
  have contextNext : Context next original header buffer:=⟨context.geometry,(MemoryMetadata.domain metadata).trans context.domain,memory,
    (otherNext "h" (by decide)).trans ((otherReady "h" (by decide)).trans context.headerLocal),by
      change child.globals.lookup (ofString "heap_ptr")=_
      rw [globals]
      exact context.heap⟩
  exact ⟨next,contextNext,metadata,rfl,bind_lookup_same _ _ _,
    (otherNext "buf" (by decide)).trans ((otherReady "buf" (by decide)).trans buf),
    StateSteps.assign_execute ready "p" advanceExpression _ _ pReady read⟩

theorem cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64)
    (context : Context source original header buffer) (installed : OriginalCode.Installed source.code)
    (bounded : (cursor buffer).toNat≤2952790016)
    (facts : ∀ field∈firstField::baseRest,FieldFacts original header field) (optional : ∀ field∈optionalFields,FieldFacts original header field)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer 9))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer))) :
    source.clock-(evaluateHOLFiniteState source afterPointer).2.clock≤1344 := by
  have prepared:=FieldWrite.prepare source original header buffer firstField 9 context installed bounded (facts _ (by simp)) (by decide) p
  obtain ⟨values,program,callee,args,called,price,back⟩:=prepared
  rw [afterPointer]
  apply ClockCost.scoped_reached_current source "w" .one (ofString "rlp_encode_bytes") (arguments firstField) values program afterFirst callee .one 52 1291 args called price
  intro child value normal checked
  obtain ⟨encoded,positive,upper,answer,metadata,memory⟩:=back child value normal
  subst value
  obtain ⟨next,nextContext,nextMetadata,clock,nextP,nextBuf,advanced⟩:=advance_returned source child original header buffer encoded context metadata memory p buf
  have nextInstalled : OriginalCode.Installed next.code:=by rw [MemoryMetadata.code nextMetadata]; exact installed
  have nextPrice:=HeaderRest.cost next original header buffer (9+encoded) nextContext nextInstalled bounded
    (by intro field member; exact facts field (List.mem_cons_of_mem _ member)) optional (by omega) (by change encoded≤41 at upper; omega) nextP nextBuf
  rw [afterFirst,StateSteps.next_sequence _ next _ _ advanced (by rw [clock]; exact Nat.le_refl _)]
  rw [clock] at nextPrice
  exact nextPrice

theorem normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (original : Memory) (header buffer : BitVec 64)
    (context : Context source original header buffer) (installed : OriginalCode.Installed source.code)
    (bounded : (cursor buffer).toNat≤2952790016)
    (facts : ∀ field∈firstField::baseRest,FieldFacts original header field) (optional : ∀ field∈optionalFields,FieldFacts original header field)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (address buffer 9))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (value : ValueHOL 64) (returned : evaluateHOLFiniteState source afterPointer=(some (.returned value),target)) :
    ∃ start encoded,1≤encoded ∧ encoded≤916 ∧ value=encodedPair start encoded ∧ AllocatedBytes.Arena start encoded ∧
      MemoryMetadata.erase target=MemoryMetadata.erase source ∧ OldMemory target.memory original buffer := by
  have prepared:=FieldWrite.prepare source original header buffer firstField 9 context installed bounded (facts _ (by simp)) (by decide) p
  obtain ⟨values,program,callee,args,called,price,back⟩:=prepared
  obtain ⟨funded,child,childValue,inner,bodyRun,checked,remaining,endpoint⟩:=CallNormal.scoped_normal source target "w" .one (ofString "rlp_encode_bytes")
    (arguments firstField) values program afterFirst callee .one args called value returned
  obtain ⟨firstEncoded,positive,upper,answer,metadata,memory⟩:=back child childValue bodyRun
  subst childValue
  obtain ⟨next,nextContext,nextMetadata,clock,nextP,nextBuf,advanced⟩:=advance_returned source child original header buffer firstEncoded context metadata memory p buf
  rw [afterFirst,StateSteps.next_sequence _ next _ _ advanced (by rw [clock]; exact Nat.le_refl _)] at remaining
  have nextInstalled : OriginalCode.Installed next.code:=by rw [MemoryMetadata.code nextMetadata]; exact installed
  obtain ⟨start,encoded,positive,size,answer,arena,metadata,memory⟩:=HeaderRest.normal next inner original header buffer (9+firstEncoded)
    nextContext nextInstalled bounded (by intro field member; exact facts field (List.mem_cons_of_mem _ member)) optional
    (by omega) (by change firstEncoded≤41 at upper; omega) nextP nextBuf value remaining
  rw [endpoint]
  exact ⟨start,encoded,positive,size,answer,arena,metadata.trans nextMetadata,memory⟩

end InitECandidate.Solver.Input.CurrentRlp.HeaderFirst

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderFirst.advance_returned
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderFirst.cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderFirst.normal
