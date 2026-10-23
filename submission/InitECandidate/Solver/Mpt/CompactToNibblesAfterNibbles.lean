import InitECandidate.Solver.Mpt.CompactToNibblesAfterNormal
import InitECandidate.Solver.Mpt.CompactToNibblesOddNibbles

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Follow the real post-allocation compact decoder through its optional
first nibble, original long converter call and actual tuple return. Every
returned path byte is a nibble, including the shared-word first byte. -/
theorem after_allocation_nibbles (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer out odd leaf : BitVec 64) (byte : BitVec 8) (length : Nat) (positive : 1≤length) (bounded : length≤1024)
    (domain : source.memaddrs=InitE.ordinaryDomain) (little : source.be=false)
    (arena : AllocatedBytes.Arena out (2*length)) (inputArena : AllocatedBytes.Arena pointer length)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (oddCell : source.locals.lookup (ofString "odd")=some (.val (.word odd)))
    (leafCell : source.locals.lookup (ofString "is_leaf")=some (.val (.word leaf)))
    (byteCell : source.locals.lookup (ofString "c0")=some (.val (.word (BitVec.ofNat 64 byte.toNat))))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterAllocation=(some (.returned value),target)) :
    ∃ nibbles : Nat,nibbles≤2*length ∧ value=output out nibbles leaf ∧ KeyToNibbles.NibblePrefix target out nibbles := by
  have difference : BitVec.ofNat 64 length-1#64=BitVec.ofNat 64 (length-1):=BitVec.ofNat_sub_ofNat_of_le length 1 (by decide) positive
  rw [after_allocation_shape] at normal
  obtain ⟨declared,inner,read,checked,continued,endpoint⟩:=Input.CallNormal.declaration_normal_entry source target "k" .one (.const 0#64) _ value normal
  have declaredEq : declared=.val (.word 0#64):=Option.some.inj read.symm
  subst declared
  let current:=bind source "k" 0#64
  have saved (name : String) (different : ofString "k"≠ofString name) : current.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    bind_lookup_other source "k" name 0#64 different
  obtain ⟨middle,oddRun,afterRun⟩:=Input.sequence_returned current inner oddGuard afterOdd value (odd_no_return current) continued
  obtain ⟨k,binary,kCell,nextPointer,nextLength,nextOut⟩:=odd_normal current middle pointer (BitVec.ofNat 64 length) out odd
    ((saved "p" (by decide)).trans pointerCell) ((saved "n" (by decide)).trans lengthCell) ((saved "out" (by decide)).trans outCell)
    ((saved "odd" (by decide)).trans oddCell) (bind_lookup_same _ _ _) oddRun
  obtain ⟨nibbleK,nibbleBinary,nibbleCell,prefixNibbles⟩:=odd_nibbles current middle out odd byte
    ((saved "out" (by decide)).trans outCell) ((saved "odd" (by decide)).trans oddCell) ((saved "c0" (by decide)).trans byteCell)
    (bind_lookup_same _ _ _) little (by simpa only [byteAddress,BitVec.add_zero] using AllocatedBytes.byte_mapped current out (2*length) 0 domain arena (by omega)) oddRun
  have sameK : nibbleK=k:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (nibbleCell.symm.trans kCell)))
  subst nibbleK
  have kBound : k.toNat≤1:=by
    rcases binary with zero|one
    · rw [zero]; decide
    · rw [one]; decide
  let nibbles:=k.toNat+2*(length-1)
  have extent : nibbles≤2*length:=by dsimp only [nibbles]; omega
  have runtime:=Input.evaluation_fields current middle oddGuard none oddRun
  have middleDomain : middle.memaddrs=InitE.ordinaryDomain:=runtime.1.trans domain
  have middleLittle : middle.be=false:=runtime.2.1.trans little
  have middleInstalled : Input.OriginalCode.Installed middle.code:=by rw [runtime.2.2.2]; exact installed
  have args : evalListHOLFinite middle (h:=fun query=>Classical.propDecidable (middle.memaddrs query)) keyArguments=
      some (KeyToNibbles.anyValues (pointer+1#64) (BitVec.ofNat 64 (length-1)) (out+BitVec.ofNat 64 k.toNat)):=by
    simp [keyArguments,KeyToNibbles.anyValues,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,nextPointer,nextLength,nextOut,kCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,difference]
  obtain ⟨last,keyRun,returnRun⟩:=Input.sequence_returned middle inner keyCall footer value
    (Input.NoReturn.ignored_call (ofString "key_to_nibbles") keyArguments middle) afterRun
  have suffixArena : AllocatedBytes.Arena (pointer+1#64) (length-1):=by
    simpa only [byteAddress] using AllocatedBytes.Arena.subrange pointer length 1 (length-1) inputArena (by omega)
  obtain ⟨nibblesWritten,price⟩:=KeyToNibbles.prefixed_call_normal middle last (pointer+1#64) out k.toNat (length-1) (by omega) keyArguments args middleInstalled middleLittle
    (by have upper:=arena.upper; omega)
    (by intro offset inside; exact AllocatedBytes.byte_mapped middle out (2*length) offset middleDomain arena (by change offset<nibbles at inside; omega))
    (by intro offset inside; exact AllocatedBytes.byte_mapped middle (pointer+1#64) (length-1) offset middleDomain suffixArena inside) prefixNibbles keyRun
  have kept (name : MlS) : last.locals.lookup name=middle.locals.lookup name:=by
    have safe : Input.LocalPrefix name keyCall:=.call none _ _ (by intro destination impossible; cases impossible)
    have info:=safe.summary_full middle
    unfold Input.LocalSummary at info
    rw [keyRun] at info
    exact info.1 rfl
  have leafInfo:=odd_local_summary (ofString "is_leaf") (by decide) current
  unfold Input.LocalSummary at leafInfo
  rw [oddRun] at leafInfo
  have nextLeaf : middle.locals.lookup (ofString "is_leaf")=some (.val (.word leaf)):=(leafInfo.1 rfl).trans ((saved "is_leaf" (by decide)).trans leafCell)
  have wordNumber : k+2#64*(BitVec.ofNat 64 length-1#64)=BitVec.ofNat 64 nibbles:=by
    simp only [nibbles,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.ofNat_toNat,BitVec.setWidth_eq,difference]
  have actual : eval last resultExpression=some (output out nibbles leaf):=by
    simp [eval,resultExpression,output,evalHOLExact,evalListHOLExact,localVar,toExact,(kept _).trans nextOut,(kept _).trans nextLength,
      (kept _).trans kCell,(kept _).trans nextLeaf,valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,wordNumber]
  obtain ⟨returned,innerEq⟩:=Input.return_normal last inner resultExpression value returnRun
  refine ⟨nibbles,extent,Option.some.inj (returned.symm.trans actual),?_⟩
  rw [endpoint,innerEq]
  exact nibblesWritten

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.after_allocation_nibbles
