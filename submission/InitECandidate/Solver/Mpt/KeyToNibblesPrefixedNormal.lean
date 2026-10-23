import InitECandidate.Solver.Mpt.KeyToNibblesPrefixedLoops
import InitECandidate.Solver.ClockPadding

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem prefixed_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64)
    (leading length : Nat) (small : length≤1024)
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word (out+BitVec.ofNat 64 leading))))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (little : source.be=false) (fits : out.toNat+(leading+2*length)<2^64)
    (mapped : ∀ offset<leading+2*length,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress out offset)))
    (inputMapped : ∀ offset<length,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress key offset)))
    (prior : NibblePrefix source out leading) (enough : length+3≤source.clock) :
    ∃ post,evaluateHOLFiniteState source body=(some (.returned (.val (.word 0#64))),post) ∧ NibblePrefix post out (leading+2*length) := by
  let entered:=bind source "i" 0#64
  have ready : PrefixedReady entered key out leading length 0 0:=by
    refine ⟨?_,?_,bind_lookup_same _ _ _,?_,little,by omega,small,fits,mapped,inputMapped,?_⟩
    · exact (bind_lookup_other source "i" "key" 0#64 (by decide)).trans keyCell
    · exact (bind_lookup_other source "i" "out" 0#64 (by decide)).trans outCell
    · exact (bind_lookup_other source "i" "n" 0#64 (by decide)).trans lengthCell
    · change NibblePrefix source out (leading+2*(0+0))
      simpa only [Nat.zero_add,Nat.mul_zero,Nat.add_zero] using prior
  obtain ⟨middle,index,blockPaid,blockRun,middleReady,remainder,blockBound,blockClock⟩:=
    prefixed_loop_execute blockCondition blockBody 4 length (by decide) key out leading (block_reads length (by omega))
      (fun current index valid room=>prefixed_block_execute current key out leading length index valid room) entered 0 ready
      (by change length-0≤source.clock; omega)
  change middle.clock=source.clock-blockPaid at blockClock
  obtain ⟨last,next,tailPaid,tailRun,lastReady,finished,tailBound,tailClock⟩:=
    prefixed_loop_execute tailCondition tailBody 1 length (by decide) key out leading (tail_reads length (by omega))
      (fun current index valid room=>prefixed_tail_execute current key out leading length index valid room) middle index middleReady (by omega)
  have finalIndex : next=length:=by have inside:=lastReady.inside; omega
  subst next
  rw [←loop_shapes.1] at blockRun
  rw [←loop_shapes.2] at tailRun
  have finalRun : evaluateHOLFiniteState last afterTail=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite last):=by
    rw [after_tail_shape]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have remainderRun : evaluateHOLFiniteState middle (.seq tailLoop afterTail)=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite last):=by
    rw [evaluateHOLFiniteState_seq_line780,tailRun]
    exact finalRun
  have innerRun : evaluateHOLFiniteState entered (.seq blockLoop (.seq tailLoop afterTail))=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite last):=by
    rw [evaluateHOLFiniteState_seq_line780,blockRun]
    exact remainderRun
  have whole:=Input.ScalarScope.declare_execute source (emptyLocalsHOLFinite last) "i" (.const 0#64) 0#64 _
    (some (.returned (.val (.word 0#64)))) rfl innerRun
  rw [←body_shape] at whole
  refine ⟨restore source "i" (emptyLocalsHOLFinite last),whole,?_⟩
  change NibblePrefix last out (leading+2*length)
  simpa only [Nat.add_zero] using lastReady.nibbles

/-- A real normal original conversion returns0 and writes only nibble
values, for every input length up to1024. An existing compact-path prefix
survives. No future successful execution, input/output separation, fixed
input-byte snapshot, or initial clock funding is assumed. -/
theorem prefixed_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64)
    (leading length : Nat) (small : length≤1024)
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word (out+BitVec.ofNat 64 leading))))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (little : source.be=false) (fits : out.toNat+(leading+2*length)<2^64)
    (mapped : ∀ offset<leading+2*length,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress out offset)))
    (inputMapped : ∀ offset<length,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress key offset)))
    (prior : NibblePrefix source out leading) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    value=.val (.word 0#64) ∧ NibblePrefix target out (leading+2*length) := by
  let extra:=length+3
  let padded:={source with clock:=source.clock+extra}
  obtain ⟨post,actual,nibbles⟩:=prefixed_execute padded key out leading length small keyCell outCell lengthCell little fits mapped inputMapped prior
    (by change length+3≤source.clock+extra; omega)
  have lifted:=panPropsEvaluateAddClockEq body source (some (.returned value)) target extra ⟨normal,by intro impossible; cases impossible⟩
  have joined:=lifted.symm.trans actual
  have resultEq:=congrArg Prod.fst joined
  have postEq:=congrArg Prod.snd joined
  change {target with clock:=target.clock+extra}=post at postEq
  rw [←postEq] at nibbles
  exact ⟨by simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using resultEq,nibbles⟩

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.prefixed_execute
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.prefixed_normal
