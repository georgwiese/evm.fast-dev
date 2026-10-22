import InitECandidate.Solver.Mpt.KeyToNibblesSmallLoops

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Execute both unchanged loops for every key length up to32. Only the
actual two-times-length output span must be mapped. -/
theorem small_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64)
    (length : Nat) (small : length≤32) (bytes : Nat→BitVec 8)
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (little : source.be=false) (fits : out.toNat+64<2^64)
    (mapped : ∀ offset<2*length,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress out offset)))
    (input : ByteRegion.Reads source key length bytes)
    (separate : ∀ left<length,∀ right<2*length,byteAddress key left≠byteAddress out right)
    (enough : length+3≤source.clock) :
    ∃ post,evaluateHOLFiniteState source body=(some (.returned (.val (.word 0#64))),post) ∧
      TrieWalk.KeyView post.memory post.memaddrs post.be out (2*length) ∧
      source.clock-post.clock≤length+3 ∧ OutputFrame source post out := by
  let entered:=bind source "i" 0#64
  have ready : SmallReady entered key out length 0 0 bytes:=by
    refine ⟨?_,?_,bind_lookup_same _ _ _,?_,little,by omega,small,fits,mapped,input,separate,?_⟩
    · exact (bind_lookup_other source "i" "key" 0#64 (by decide)).trans keyCell
    · exact (bind_lookup_other source "i" "out" 0#64 (by decide)).trans outCell
    · exact (bind_lookup_other source "i" "n" 0#64 (by decide)).trans lengthCell
    · intro offset impossible
      omega
  obtain ⟨middle,index,blockPaid,blockRun,middleReady,remainder,blockBound,blockClock,blockFrame⟩:=
    small_loop_execute blockCondition blockBody 4 length (by decide) key out bytes (block_reads length (by omega))
      (fun current index valid room=>small_block_execute current key out length index bytes valid room)
      entered 0 ready (by change length-0≤source.clock; omega)
  change middle.clock=source.clock-blockPaid at blockClock
  obtain ⟨last,next,tailPaid,tailRun,lastReady,finished,tailBound,tailClock,tailFrame⟩:=
    small_loop_execute tailCondition tailBody 1 length (by decide) key out bytes (tail_reads length (by omega))
      (fun current index valid room=>small_tail_execute current key out length index bytes valid room)
      middle index middleReady (by omega)
  have finalIndex : next=length:=by have inside:=lastReady.inside; omega
  subst next
  rw [←loop_shapes.1] at blockRun
  rw [←loop_shapes.2] at tailRun
  have finalRun : evaluateHOLFiniteState last afterTail=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite last):=by
    rw [after_tail_shape]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have remainderRun : evaluateHOLFiniteState middle (.seq tailLoop afterTail)=
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite last):=by
    rw [evaluateHOLFiniteState_seq_line780,tailRun]
    exact finalRun
  have innerRun : evaluateHOLFiniteState entered (.seq blockLoop (.seq tailLoop afterTail))=
      (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite last):=by
    rw [evaluateHOLFiniteState_seq_line780,blockRun]
    exact remainderRun
  have whole:=Input.ScalarScope.declare_execute source (emptyLocalsHOLFinite last) "i" (.const 0#64) 0#64 _
    (some (.returned (.val (.word 0#64)))) rfl innerRun
  rw [←body_shape] at whole
  refine ⟨restore source "i" (emptyLocalsHOLFinite last),whole,?_,?_,?_⟩
  · refine ⟨by omega,by omega,lastReady.mapped,?_⟩
    change NibblePrefix last out (2*length)
    simpa only [Nat.add_zero] using lastReady.nibbles
  · change source.clock-last.clock≤length+3
    omega
  · have frame:=OutputFrame.trans entered middle last out blockFrame tailFrame
    exact ⟨frame.fields,frame.memory⟩

theorem small_execute_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64)
    (length : Nat) (small : length≤32)
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (little : source.be=false) (fits : out.toNat+64<2^64)
    (inputMapped : ∀ offset<length,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress key offset)))
    (outputMapped : ∀ offset<2*length,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress out offset)))
    (separate : ∀ left<length,∀ right<2*length,byteAddress key left≠byteAddress out right)
    (enough : length+3≤source.clock) :
    ∃ post,evaluateHOLFiniteState source body=(some (.returned (.val (.word 0#64))),post) ∧
      TrieWalk.KeyView post.memory post.memaddrs post.be out (2*length) ∧
      source.clock-post.clock≤length+3 ∧ OutputFrame source post out :=
  small_execute source key out length small (fun offset=>ByteRegion.value source (byteAddress key offset)) keyCell outCell lengthCell little fits outputMapped
    (ByteRegion.mapped_region source key length inputMapped) separate enough

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.small_execute
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.small_execute_mapped
