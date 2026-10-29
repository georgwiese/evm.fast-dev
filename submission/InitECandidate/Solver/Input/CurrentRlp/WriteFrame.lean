import InitECandidate.Solver.Input.CurrentRlp.PutBe
import InitECandidate.Solver.Input.MemoryMetadata
import InitECandidate.Solver.Input.ByteStoreFrame
import InitECandidate.Solver.Input.LoopSummaryInvariant
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.WitnessRadix.CopyGeneralMemory
import InitECandidate.Solver.Input.IgnoredCallTarget

namespace InitECandidate.Solver.Input.CurrentRlp
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A normal byte writer changes only its actual bounded destination span.
All other runtime fields, including every global and the FFI, are retained. -/
structure WriteFrame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64) (length : Nat) : Prop where
  metadata : MemoryMetadata.erase target=MemoryMetadata.erase source
  memory : ∀ query,CopyGeneral.Away dst query length→target.memory query=source.memory query

theorem WriteFrame.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64) (length : Nat) : WriteFrame source source dst length:=
  ⟨rfl,by intros; rfl⟩

theorem WriteFrame.trans {source middle target : PanSemStateFiniteExact 64 Guest.HostMemory} {dst : BitVec 64} {length : Nat}
    (first : WriteFrame source middle dst length) (second : WriteFrame middle target dst length) : WriteFrame source target dst length:=
  ⟨second.metadata.trans first.metadata,fun query away=>(second.memory query away).trans (first.memory query away)⟩

theorem WriteFrame.readonly {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (dst : BitVec 64) (length : Nat)
    (frame : LocalEffects.erase target=LocalEffects.erase source) : WriteFrame source target dst length:=
  ⟨MemoryMetadata.of_frame frame,fun query away=>congrFun (LocalEffects.memory_of_erase source target frame) query⟩

theorem WriteFrame.weaken {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {dst : BitVec 64} {small large : Nat}
    (frame : WriteFrame source target dst small) (bounded : small≤large) : WriteFrame source target dst large:=
  ⟨frame.metadata,fun query away=>frame.memory query (fun offset inside=>away offset (Nat.lt_of_lt_of_le inside bounded))⟩

theorem WriteFrame.byte (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst index : BitVec 64) (length : Nat)
    (inside : index.toNat<length) (destination expression : ExpHOL 64)
    (read : eval source destination=some (.val (.word (dst+index))))
    (normal : evaluateHOLFiniteState source (.storeByte destination expression)=(none,target)) : WriteFrame source target dst length := by
  have frame:=byte_store_normal_frame source target destination expression (dst+index) read normal
  refine ⟨by rw [frame.1]; rfl,?_⟩
  intro query away
  apply frame.2
  have scalar : BitVec.ofNat 64 index.toNat=index:=by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt index.isLt]
  simpa only [byteAddress,scalar] using (away index.toNat inside).2


/-- Move a real smaller write span into its enclosing destination span.
Address equalities are bitvector identities, without an overflow premise. -/
theorem WriteFrame.shift {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (dst : BitVec 64) (offset length limit : Nat)
    (frame : WriteFrame source target (dst+BitVec.ofNat 64 offset) length) (inside : offset+length≤limit) :
    WriteFrame source target dst limit := by
  refine ⟨frame.metadata,?_⟩
  intro query away
  apply frame.memory query
  intro index bounded
  simpa only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc] using away (offset+index) (by omega)

/-- Lift the frame of the actual callee return through the ignored caller's
real local restoration. Normality is used only for that same observed call. -/
theorem WriteFrame.ignored (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (function : MlS) (arguments : List (ExpHOL 64))
    (values : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (dst : BitVec 64) (length : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,shape))
    (frame : ∀ target value,evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned value),target)→
      WriteFrame (callEntryStateHOLFinite source callee) target dst length)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) function arguments)=(none,post)) : WriteFrame source post dst length := by
  obtain ⟨funded,target,returned,bodyRun⟩:=CallNormal.ignored_callee_return source post function arguments values body callee shape args called normal
  have physical:=frame target returned bodyRun
  have endpoint:=CallNormal.ignored_target source post function arguments values body callee shape args called returned target bodyRun normal
  rw [endpoint]
  exact ⟨physical.metadata,physical.memory⟩

namespace PutBe
open RlpWrite.PutBe hiding body

/-- The real decrement/store/shift body protects every word outside the
counted destination, without assuming the store would succeed in advance. -/
theorem step_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst index : BitVec 64) (length : Nat)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (positive : 0<index.toNat) (bounded : index.toNat≤length)
    (normal : evaluateHOLFiniteState source loopBody=(none,target)) : WriteFrame source target dst length := by
  obtain ⟨middle,assigned,tailRun⟩:=sequence_none source target _ _ normal
  have subRead : eval source decrement=some (.val (.word (index-1#64))):=by
    simp [eval,decrement,evalHOLExact,evalListHOLExact,toExact,localVar,i,valueIsWord,valueWord,wordOpHOL,wordOp]
  have middleEq:=assign_none source middle "i" decrement (index-1#64) subRead assigned
  have firstErase:=LocalEffects.assign source.code (ofString "i") decrement source rfl
  rw [assigned] at firstErase
  have first : WriteFrame source middle dst length:=WriteFrame.readonly dst length firstErase
  obtain ⟨written,stored,shiftedRun⟩:=sequence_none middle target _ _ tailRun
  have middleD : middle.locals.lookup (ofString "dst")=some (.val (.word dst)):=by
    rw [middleEq]
    exact (bind_lookup_other source "i" "dst" _ (by decide)).trans d
  have middleI : middle.locals.lookup (ofString "i")=some (.val (.word (index-1#64))):=by rw [middleEq]; exact bind_lookup_same _ _ _
  have addressRead : eval middle address=some (.val (.word (dst+(index-1#64)))):=by
    simp [eval,address,evalHOLExact,evalListHOLExact,toExact,localVar,middleD,middleI,valueIsWord,valueWord,wordOpHOL,wordOp]
  have number : (index-1#64).toNat=index.toNat-1:=by rw [BitVec.toNat_sub_of_le (by change 1≤index.toNat; omega)]; rfl
  have second:=WriteFrame.byte middle written dst (index-1#64) length (by rw [number]; omega) address (localVar "v") addressRead stored
  have lastErase:=LocalEffects.assign written.code (ofString "v") shifted written rfl
  rw [shiftedRun] at lastErase
  exact (first.trans second).trans (WriteFrame.readonly dst length lastErase)

/-- Normal loop exits retain the current bounded counter and earlier
memory frame through each actual store; aborted bodies need no invariant. -/
theorem loop_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst index : BitVec 64) (length : Nat)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word index))) (bounded : index.toNat≤length)
    (normal : evaluateHOLFiniteState source loop=(none,target)) : WriteFrame source target dst length := by
  let invariant (current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop:=
    ∃ currentIndex : BitVec 64,current.locals.lookup (ofString "i")=some (.val (.word currentIndex)) ∧ currentIndex.toNat≤length ∧
      current.locals.lookup (ofString "dst")=some (.val (.word dst)) ∧ WriteFrame source current dst length
  have reached:=loop_invariant_summary source.code (ofString "n") test loopBody (body_summary (ofString "n") (by decide) (by decide)) invariant (by
    intro current codeEq ready word read nonzero funded post bodyRun
    obtain ⟨currentIndex,indexCell,inside,dstCell,earlier⟩:=ready
    have progress:=step_progress current ⟨currentIndex,indexCell⟩ word read nonzero
    have positive : 0<currentIndex.toNat:=by simpa only [rank,CounterFlow.counterWord,indexCell,Option.getD_some,valueWord] using progress.1
    have next:=progress.2 funded
    rw [bodyRun] at next
    obtain ⟨⟨nextIndex,nextCell⟩,smaller⟩:=next (Or.inl rfl)
    change post.locals.lookup (ofString "i")=some (.val (.word nextIndex)) at nextCell
    have oldRank : rank current=currentIndex.toNat:=by simp [rank,CounterFlow.counterWord,indexCell,valueWord]
    have newRank : rank post=nextIndex.toNat:=by simp [rank,CounterFlow.counterWord,nextCell,valueWord]
    change rank post<rank current at smaller
    rw [oldRank,newRank] at smaller
    have kept:=body_summary (ofString "dst") (by decide) (by decide) (decClockHOLFinite current)
    unfold LocalSummary at kept
    rw [bodyRun] at kept
    have delta:=step_frame (decClockHOLFinite current) post dst currentIndex length dstCell indexCell positive inside bodyRun
    have currentFrame : WriteFrame current post dst length:=⟨delta.metadata,delta.memory⟩
    exact ⟨nextIndex,nextCell,by omega,(kept.1 rfl).trans dstCell,earlier.trans currentFrame⟩)
    source target rfl ⟨index,i,bounded,d,WriteFrame.refl source dst length⟩ normal
  obtain ⟨_,_,_,_,frame⟩:=reached
  exact frame

/-- A true current put_be return is zero, costs at most its real byte
count and has only the bounded destination memory effect. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (dst : BitVec 64) (length : Nat) (small : length<2^64)
    (d : source.locals.lookup (ofString "dst")=some (.val (.word dst)))
    (n : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    value=.val (.word 0#64) ∧ source.clock-target.clock≤length ∧ WriteFrame source target dst length := by
  have price:=body_cost source (BitVec.ofNat 64 length) n
  rw [normal,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at price
  have shaped:=normal
  rw [current_body,body_shape] at shaped
  have readN : eval source (localVar "n")=some (.val (.word (BitVec.ofNat 64 length))):=by simpa only [eval,evalHOLExact,toExact,localVar] using n
  obtain ⟨inner,continued,endpoint⟩:=declaration_return_word source target "i" (localVar "n") (BitVec.ofNat 64 length) tail value readN shaped
  let entered:=bind source "i" (BitVec.ofNat 64 length)
  change evaluateHOLFiniteState entered (.seq loop (.return (.const 0#64)))=(some (.returned value),inner) at continued
  have never:=(while_local_summary (ofString "n") test loopBody (body_summary (ofString "n") (by decide) (by decide)) entered).2.1
  obtain ⟨last,loopRun,returnRun⟩:=sequence_returned entered inner loop (.return (.const 0#64)) value never continued
  have frame:=loop_frame entered last dst (BitVec.ofNat 64 length) length ((bind_lookup_other source "i" "dst" _ (by decide)).trans d) (bind_lookup_same _ _ _)
    (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]) loopRun
  obtain ⟨returned,returnEnd⟩:=return_normal last inner (.const 0#64) value returnRun
  have answer : value=.val (.word 0#64):=Option.some.inj returned.symm
  have finalFrame : WriteFrame last target dst length:=by rw [endpoint,returnEnd]; exact ⟨rfl,by intros; rfl⟩
  have fromSource : WriteFrame source last dst length:=⟨frame.metadata,frame.memory⟩
  exact ⟨answer,price,fromSource.trans finalFrame⟩


/-- The original current ignored call retains the callee's bounded memory
frame and every nonlocal; its real caller locals are restored by the ABI. -/
theorem call_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64))
    (dst word : BitVec 64) (length : Nat) (small : length<2^64) (installed : OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word dst),.val (.word word),.val (.word (BitVec.ofNat 64 length))])
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_put_be") arguments)=(none,post)) : WriteFrame source post dst length := by
  obtain ⟨callee,called,d,v,n⟩:=environment source.code.lookup dst word (BitVec.ofNat 64 length) (original_code source.code installed)
  apply WriteFrame.ignored source post (ofString "rlp_put_be") arguments _ body callee .one dst length args called
  · intro target value run
    exact (body_normal (callEntryStateHOLFinite source callee) target dst length small d n value run).2.2
  · exact normal

end PutBe
end InitECandidate.Solver.Input.CurrentRlp

#print axioms InitECandidate.Solver.Input.CurrentRlp.WriteFrame.refl
#print axioms InitECandidate.Solver.Input.CurrentRlp.WriteFrame.trans
#print axioms InitECandidate.Solver.Input.CurrentRlp.WriteFrame.readonly
#print axioms InitECandidate.Solver.Input.CurrentRlp.WriteFrame.weaken
#print axioms InitECandidate.Solver.Input.CurrentRlp.WriteFrame.byte
#print axioms InitECandidate.Solver.Input.CurrentRlp.PutBe.step_frame
#print axioms InitECandidate.Solver.Input.CurrentRlp.PutBe.loop_frame
#print axioms InitECandidate.Solver.Input.CurrentRlp.PutBe.body_normal

#print axioms InitECandidate.Solver.Input.CurrentRlp.WriteFrame.shift

#print axioms InitECandidate.Solver.Input.CurrentRlp.WriteFrame.ignored

#print axioms InitECandidate.Solver.Input.CurrentRlp.PutBe.call_frame
