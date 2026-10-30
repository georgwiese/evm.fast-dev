import InitECandidate.Solver.Input.ScopedCallData
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

namespace InitECandidate.Solver.Input.CurrentRlp.HeaderFirst
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch HeaderEncoding

/-- Resolve only the genuine first field reads and original three-word ABI.
The fixed length and actual output cursor follow from those same reads. -/
theorem current_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer : BitVec 64)
    (values : List (ValueHOL 64)) (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (installed : OriginalCode.Installed source.code)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (BitVec.ofNat 64 (buffer.toNat+9)))))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (arguments firstField)=some values)
    (called : lookupCodeHOLFinite source.code.lookup (ofString "rlp_encode_bytes") values=some (actual,callee,shape)) :
    ∃ src : BitVec 64,actual=BytesWrite.body ∧
      callee.lookup (ofString "dst")=some (.val (.word (BitVec.ofNat 64 (buffer.toNat+9)))) ∧
      callee.lookup (ofString "src")=some (.val (.word src)) ∧ callee.lookup (ofString "n")=some (.val (.word 32#64)) := by
  obtain ⟨dst,src,count,valuesEq,firstRead,secondRead,thirdRead,bodyEq,d,s,n⟩:=BytesWrite.current_argument_entry source
    (localVar "p") (loadOne 8) (.const 32#64) values actual callee shape installed args called
  have dstEq : dst=BitVec.ofNat 64 (buffer.toNat+9):=by
    simpa only [eval,evalHOLExact,toExact,localVar,p,Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using firstRead.symm
  have countEq : count=32#64:=by
    simpa only [eval,evalHOLExact,Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using thirdRead.symm
  subst dst
  subst count
  exact ⟨src,bodyEq,d,s,n⟩

/-- A real first byte-child return gives its short fixed-field size and
protected prefix. Install that actual word and perform the real advance. -/
theorem current_advance (source child : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer src : BitVec 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returned : ValueHOL 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (reserved : AllocatedBytes.Arena buffer 18) (aligned : buffer.toNat%8=0)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (BitVec.ofNat 64 (buffer.toNat+9)))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (d : callee.lookup (ofString "dst")=some (.val (.word (BitVec.ofNat 64 (buffer.toNat+9)))))
    (s : callee.lookup (ofString "src")=some (.val (.word src))) (n : callee.lookup (ofString "n")=some (.val (.word 32#64)))
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) BytesWrite.body=(some (.returned returned),child)) :
    ∃ encoded next,1≤encoded ∧ encoded≤41 ∧ MemoryMetadata.erase next=MemoryMetadata.erase source ∧
      (∀ query : BitVec 64,query.toNat<buffer.toNat→next.memory query=source.memory query) ∧ next.clock=child.clock ∧
      next.locals.lookup (ofString "p")=some (.val (.word (BitVec.ofNat 64 (buffer.toNat+9+encoded)))) ∧
      next.locals.lookup (ofString "buf")=some (.val (.word buffer)) ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source child "w" returned) advance=(none,next) := by
  have bufferLower:=reserved.lower
  have bufferUpper:=reserved.upper
  have pointerNumber : (BitVec.ofNat 64 (buffer.toNat+9)).toNat=buffer.toNat+9:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨encoded,positive,upper,uniform,answer,metadata,memory⟩:=BytesWrite.body_current_normal (callEntryStateHOLFinite source callee) child
    (BitVec.ofNat 64 (buffer.toNat+9)) src 32#64 0#64 buffer.toNat installed domain d s n
    (by rw [pointerNumber]; omega) aligned (by rw [pointerNumber]; omega) (by change 0<buffer.toNat; omega) returned run
  have small : encoded≤41:=by change encoded≤32+9 at upper; omega
  let ready:=CallNormal.continuationEntry source child "w" returned
  have pR : ready.locals.lookup (ofString "p")=some (.val (.word (BitVec.ofNat 64 (buffer.toNat+9)))):=
    (CallNormal.continuation_lookup_other source child "w" "p" returned (by decide)).trans p
  have wR : ready.locals.lookup (ofString "w")=some (.val (.word (BitVec.ofNat 64 encoded))):=
    (CallNormal.continuation_lookup_same source child "w" returned).trans (congrArg some answer)
  have read : eval ready advanceExpression=some (.val (.word (BitVec.ofNat 64 (buffer.toNat+9+encoded)))):=by
    simp [eval,advanceExpression,localVar,evalHOLExact,evalListHOLExact,toExact,pR,wR,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  let next:=bind ready "p" (BitVec.ofNat 64 (buffer.toNat+9+encoded))
  have advanced:=StateSteps.assign_execute ready "p" advanceExpression _ _ pR read
  refine ⟨encoded,next,positive,small,metadata,?_,rfl,bind_lookup_same _ _ _,?_,advanced⟩
  · intro query before
    obtain ⟨_,_,_,_,_,_,earlier⟩:=BytesWrite.body_current_normal (callEntryStateHOLFinite source callee) child
      (BitVec.ofNat 64 (buffer.toNat+9)) src 32#64 query buffer.toNat installed domain d s n
      (by rw [pointerNumber]; omega) aligned (by rw [pointerNumber]; omega) before returned run
    exact earlier
  · exact (bind_lookup_other _ "p" "buf" _ (by decide)).trans
      ((CallNormal.continuation_lookup_other source child "w" "buf" returned (by decide)).trans buf)

/-- Every outcome of the original first scoped call and all later fields,
without a decoded parent image or successful-read premise. -/
theorem current_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤2952790016)
    (reserved : AllocatedBytes.Arena buffer 18) (aligned : buffer.toNat%8=0) (beforeHeap : buffer.toNat≤heap.toNat)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (BitVec.ofNat 64 (buffer.toNat+9)))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer))) :
    source.clock-(evaluateHOLFiniteState source afterPointer).2.clock≤43314053973 := by
  rw [afterPointer]
  apply ClockCost.scoped_arguments_reached_current source "w" .one (ofString "rlp_encode_bytes") (arguments firstField) afterFirst 61 43314053911
  · intro values actual callee shape args called
    obtain ⟨src,bodyEq,d,s,n⟩:=current_entry source buffer values actual callee shape installed p args called
    rw [bodyEq]
    exact BytesWrite.body_known_length_cost (callEntryStateHOLFinite source callee) (BitVec.ofNat 64 (buffer.toNat+9)) src 32 (by decide) installed domain d s n
  · intro values actual callee shape child returned args called run checked
    obtain ⟨src,bodyEq,d,s,n⟩:=current_entry source buffer values actual callee shape installed p args called
    rw [bodyEq] at run
    obtain ⟨encoded,next,positive,small,metadata,memory,clock,nextP,nextBuf,advanced⟩:=current_advance source child buffer src callee returned installed domain reserved aligned p buf d s n run
    have nextInstalled : OriginalCode.Installed next.code:=by rw [MemoryMetadata.code metadata]; exact installed
    have nextDomain : next.memaddrs=InitE.ordinaryDomain:=(MemoryMetadata.domain metadata).trans domain
    have globals:=congrArg PanSemStateFiniteExact.globals metadata
    change next.globals=source.globals at globals
    have nextHeap : next.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
    have price:=HeaderRest.current_cost next buffer heap (buffer.toNat+9+encoded) nextInstalled nextDomain nextHeap heapLower heapBound reserved aligned beforeHeap
      (by omega) (by have bound:=reserved.upper; omega) nextP nextBuf
    rw [afterFirst,StateSteps.next_sequence _ next _ _ advanced (by rw [clock]; exact Nat.le_refl _)]
    rw [clock] at price
    exact price

/-- Actual normal first call and base sequence supply a finite returned
span and preserve the whole earlier input prefix for the real hash. -/
theorem current_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (buffer heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤2952790016)
    (reserved : AllocatedBytes.Arena buffer 18) (aligned : buffer.toNat%8=0) (beforeHeap : buffer.toNat≤heap.toNat)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (BitVec.ofNat 64 (buffer.toNat+9)))))
    (buf : source.locals.lookup (ofString "buf")=some (.val (.word buffer)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterPointer=(some (.returned value),target)) :
    ∃ start encoded,1≤encoded ∧ encoded≤33806090619 ∧ buffer.toNat≤start.toNat ∧
      start.toNat≤buffer.toNat+8 ∧ start.toNat+encoded≤buffer.toNat+33806090619 ∧ value=encodedPair start encoded ∧
      MemoryMetadata.erase target=MemoryMetadata.erase source ∧
      (∀ query : BitVec 64,query.toNat<buffer.toNat→target.memory query=source.memory query) := by
  obtain ⟨funded,values,actual,callee,shape,child,returned,inner,args,called,run,checked,continued,endpoint⟩:=CallNormal.scoped_data source target "w" .one
    (ofString "rlp_encode_bytes") (arguments firstField) afterFirst value normal
  obtain ⟨src,bodyEq,d,s,n⟩:=current_entry source buffer values actual callee shape installed p args called
  rw [bodyEq] at run
  obtain ⟨firstEncoded,next,positive,small,metadata,memory,clock,nextP,nextBuf,advanced⟩:=current_advance source child buffer src callee returned
    installed domain reserved aligned p buf d s n run
  rw [afterFirst,StateSteps.next_sequence _ next _ _ advanced (by rw [clock]; exact Nat.le_refl _)] at continued
  have nextInstalled : OriginalCode.Installed next.code:=by rw [MemoryMetadata.code metadata]; exact installed
  have nextDomain : next.memaddrs=InitE.ordinaryDomain:=(MemoryMetadata.domain metadata).trans domain
  have globals:=congrArg PanSemStateFiniteExact.globals metadata
  change next.globals=source.globals at globals
  have nextHeap : next.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
  obtain ⟨start,encoded,encodedPositive,size,startLower,startUpper,endLower,endUpper,answer,lastMetadata,lastMemory⟩:=HeaderRest.current_normal next inner buffer heap
    (buffer.toNat+9+firstEncoded) nextInstalled nextDomain nextHeap heapLower heapBound reserved aligned beforeHeap
    (by omega) (by have bound:=reserved.upper; omega) nextP nextBuf value continued
  rw [endpoint]
  refine ⟨start,encoded,encodedPositive,by omega,startLower,startUpper,by omega,answer,lastMetadata.trans metadata,?_⟩
  intro query before
  exact (lastMemory query before).trans (memory query before)

end InitECandidate.Solver.Input.CurrentRlp.HeaderFirst

#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderFirst.current_entry
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderFirst.current_advance
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderFirst.current_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.HeaderFirst.current_normal
