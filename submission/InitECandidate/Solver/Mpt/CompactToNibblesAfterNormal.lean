import InitECandidate.Solver.Mpt.CompactToNibblesOddFrame
import InitECandidate.Solver.Mpt.KeyToNibblesSpanAllocated

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def output (pointer : BitVec 64) (length : Nat) (leaf : BitVec 64) : ValueHOL 64:=
  .rStruct [.val (.word pointer),.val (.word (BitVec.ofNat 64 length)),.val (.word leaf)]

/-- Genuine post-allocation normal compact decoding returns its actual
fresh output and at most twice the input length. Both the optional nibble
and full converter writes stay inside that same real allocation. -/
theorem after_allocation_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer out odd leaf : BitVec 64) (length : Nat) (positive : 1≤length)
    (arena : AllocatedBytes.Arena out (2*length)) (aligned : out.toNat%8=0)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (oddCell : source.locals.lookup (ofString "odd")=some (.val (.word odd)))
    (leafCell : source.locals.lookup (ofString "is_leaf")=some (.val (.word leaf)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterAllocation=(some (.returned value),target)) :
    ∃ nibbles : Nat,nibbles≤2*length ∧ value=output out nibbles leaf ∧
      KeyToNibbles.writeMetadata target=KeyToNibbles.writeMetadata source ∧
      ∀ query : BitVec 64,query.toNat<out.toNat ∨ out.toNat+2*length≤query.toNat→target.memory query=source.memory query := by
  have small : length+4<2^64:=by have upper:=arena.upper; omega
  have difference : BitVec.ofNat 64 length-1#64=BitVec.ofNat 64 (length-1):=BitVec.ofNat_sub_ofNat_of_le length 1 (by decide) positive
  rw [after_allocation_shape] at normal
  obtain ⟨declared,inner,read,checked,continued,endpoint⟩:=Input.CallNormal.declaration_normal_entry source target "k" .one (.const 0#64) _ value normal
  have declaredEq : declared=.val (.word 0#64):=Option.some.inj read.symm
  subst declared
  let current:=QueryBranch.bind source "k" 0#64
  have currentPointer : current.locals.lookup (ofString "p")=some (.val (.word pointer)):=(bind_lookup_other source "k" "p" 0#64 (by decide)).trans pointerCell
  have currentLength : current.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=(bind_lookup_other source "k" "n" 0#64 (by decide)).trans lengthCell
  have currentOut : current.locals.lookup (ofString "out")=some (.val (.word out)):=(bind_lookup_other source "k" "out" 0#64 (by decide)).trans outCell
  have currentOdd : current.locals.lookup (ofString "odd")=some (.val (.word odd)):=(bind_lookup_other source "k" "odd" 0#64 (by decide)).trans oddCell
  have currentLeaf : current.locals.lookup (ofString "is_leaf")=some (.val (.word leaf)):=(bind_lookup_other source "k" "is_leaf" 0#64 (by decide)).trans leafCell
  obtain ⟨middle,oddRun,afterRun⟩:=Input.sequence_returned current inner oddGuard afterOdd value (odd_no_return current) continued
  obtain ⟨k,binary,kCell,nextPointer,nextLength,nextOut⟩:=odd_normal current middle pointer (BitVec.ofNat 64 length) out odd currentPointer currentLength currentOut currentOdd (bind_lookup_same _ _ _) oddRun
  have leafInfo:=odd_local_summary (ofString "is_leaf") (by decide) current
  unfold Input.LocalSummary at leafInfo
  rw [oddRun] at leafInfo
  have nextLeaf : middle.locals.lookup (ofString "is_leaf")=some (.val (.word leaf)):=(leafInfo.1 rfl).trans currentLeaf
  have oddFrame:=odd_span_frame current middle out odd currentOut currentOdd oddRun
  have args : evalListHOLFinite middle (h:=fun query=>Classical.propDecidable (middle.memaddrs query)) keyArguments=
      some (KeyToNibbles.anyValues (pointer+1#64) (BitVec.ofNat 64 (length-1)) (out+k)):=by
    simp [keyArguments,KeyToNibbles.anyValues,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,nextPointer,nextLength,nextOut,kCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,difference]
  have codeEq:=(Input.evaluation_fields current middle oddGuard none oddRun).2.2.2
  have middleInstalled : Input.OriginalCode.Installed middle.code:=by rw [codeEq]; exact installed
  obtain ⟨last,keyRun,returnRun⟩:=Input.sequence_returned middle inner keyCall footer value
    (Input.NoReturn.ignored_call (ofString "key_to_nibbles") keyArguments middle) afterRun
  have keyFrame:=KeyToNibbles.call_span_frame middle last (pointer+1#64) (out+k) (length-1) (by omega) keyArguments args middleInstalled keyRun
  have kept (name : MlS) : last.locals.lookup name=middle.locals.lookup name:=by
    have safe : Input.LocalPrefix name keyCall:=.call none _ _ (by intro destination impossible; cases impossible)
    have info:=safe.summary_full middle
    unfold Input.LocalSummary at info
    rw [keyRun] at info
    exact info.1 rfl
  have lastOut : last.locals.lookup (ofString "out")=some (.val (.word out)):=(kept _).trans nextOut
  have lastLength : last.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))):=(kept _).trans nextLength
  have lastK : last.locals.lookup (ofString "k")=some (.val (.word k)):=(kept _).trans kCell
  have lastLeaf : last.locals.lookup (ofString "is_leaf")=some (.val (.word leaf)):=(kept _).trans nextLeaf
  let nibbles:=k.toNat+2*(length-1)
  have wordNumber : k+2#64*(BitVec.ofNat 64 length-1#64)=BitVec.ofNat 64 nibbles:=by
    simp only [nibbles,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.ofNat_toNat,BitVec.setWidth_eq,difference]
  have actual : eval last resultExpression=some (output out nibbles leaf):=by
    simp [eval,resultExpression,output,evalHOLExact,evalListHOLExact,localVar,toExact,lastOut,lastLength,lastK,lastLeaf,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,wordNumber]
  obtain ⟨returned,innerEq⟩:=Input.return_normal last inner resultExpression value returnRun
  have valueEq : value=output out nibbles leaf:=Option.some.inj (returned.symm.trans actual)
  have kBound : k.toNat≤1:=by
    rcases binary with zero|one
    · rw [zero]; decide
    · rw [one]; decide
  have extent : nibbles≤2*length:=by dsimp only [nibbles]; omega
  have shiftedOdd : KeyToNibbles.SpanFrame current middle (byteAddress out 0) 1:=by simpa only [byteAddress,BitVec.add_zero] using oddFrame
  have shiftedKey : KeyToNibbles.SpanFrame middle last (byteAddress out k.toNat) (2*(length-1)):=by
    simpa only [byteAddress,BitVec.ofNat_toNat,BitVec.setWidth_eq] using keyFrame
  have oddAway:=shiftedOdd.allocated_frame current middle out (2*length) 0 1 arena aligned (by omega)
  have keyAway:=shiftedKey.allocated_frame middle last out (2*length) k.toNat (2*(length-1)) arena aligned extent
  refine ⟨nibbles,extent,valueEq,?_,?_⟩
  · rw [endpoint,innerEq]
    exact keyFrame.fields.trans oddFrame.fields
  · intro query outside
    rw [endpoint,innerEq]
    exact (keyAway query outside).trans (oddAway query outside)

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.after_allocation_normal
