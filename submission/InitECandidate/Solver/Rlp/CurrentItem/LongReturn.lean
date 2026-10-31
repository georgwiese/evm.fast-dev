import InitECandidate.Solver.Rlp.ItemValueSyntax
import InitECandidate.Solver.Rlp.CurrentItem.Entry
import InitECandidate.Solver.Rlp.HeaderShortValues
import InitECandidate.Solver.Rlp.CurrentListCount.Call

namespace InitECandidate.Solver.Rlp.CurrentItem
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Item
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem long_return_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer ll payload flag : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (llCell : source.locals.lookup (ofString "ll")=some (.val (.word ll)))
    (payloadCell : source.locals.lookup (ofString "n")=some (.val (.word payload)))
    (arena : LiveArena source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (longReturn flag)=(some (.returned value),post)) :
    value=result pointer (1#64+ll) payload flag ∧ Input.LocalEffects.erase post=Input.LocalEffects.erase source := by
  have read : eval source (.rstruct [.const flag,.op .add [localVar "p",.const 1#64,localVar "ll"],localVar "n",.op .add [.const 1#64,localVar "ll",localVar "n"]])=
      some (result pointer (1#64+ll) payload flag) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,pointerCell,llCell,payloadCell,result,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.add_assoc]
  obtain ⟨actual,returned⟩ := Input.return_normal source post _ value normal
  refine ⟨Option.some.inj (actual.symm.trans read),?_⟩
  · rw [returned]; rfl

theorem long_tail_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length ll payload flag : BitVec 64)
    (entry : Entry source pointer length)
    (llCell : source.locals.lookup (ofString "ll")=some (.val (.word ll)))
    (payloadCell : source.locals.lookup (ofString "n")=some (.val (.word payload)))
    (bounded : 1+ll.toNat+payload.toNat≤length.toNat)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (longTail flag)=(some (.returned value),post)) :
    value=result pointer (1#64+ll) payload flag ∧ Frame source post ∧
      (flag=0#64 → Input.LocalEffects.erase post=Input.LocalEffects.erase source) := by
  rw [longTail] at normal
  by_cases zero : flag=0#64
  · rw [if_pos zero] at normal
    obtain ⟨same,pure⟩ := long_return_normal source post pointer ll payload flag entry.pointerCell llCell payloadCell entry.arena value normal
    exact ⟨same,Frame.of_readonly pure,fun _=>pure⟩
  · rw [if_neg zero] at normal
    obtain ⟨middle,countRun,returnRun⟩ := Input.sequence_returned source post longCount (longReturn flag) value (Input.NoReturn.ignored_call _ _ source) normal
    have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.op .add [localVar "p",.const 1#64,localVar "ll"],localVar "n"]=
        some (Header.values (pointer+1#64+ll) payload) := by
      simp [Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,entry.pointerCell,llCell,payloadCell,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.add_assoc]
    have number1 : (pointer+1#64).toNat=pointer.toNat+1 := BitVec.toNat_add_of_lt (by change pointer.toNat+1<2^64; have := entry.fits; omega)
    have number : (pointer+1#64+ll).toNat=pointer.toNat+1+ll.toNat := by
      rw [BitVec.toNat_add_of_lt (by rw [number1]; have := entry.fits; omega),number1]
    have fits : (pointer+1#64+ll).toNat+payload.toNat<2^64 := by rw [number]; have := entry.fits; omega
    have countFrame:=CurrentListCount.ignored_frame source middle (pointer+1#64+ll) payload entry.arena fits _ args countRun
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,same,_⟩ := Input.CallNormal.ignored_data source middle (ofString "rlp_list_count") _ countRun
    have locals : middle.locals=source.locals := by rw [same]
    have nextPointer : middle.locals.lookup (ofString "p")=some (.val (.word pointer)) := by rw [locals]; exact entry.pointerCell
    have nextLl : middle.locals.lookup (ofString "ll")=some (.val (.word ll)) := by rw [locals]; exact llCell
    have nextPayload : middle.locals.lookup (ofString "n")=some (.val (.word payload)) := by rw [locals]; exact payloadCell
    obtain ⟨same,returnFrame⟩:=long_return_normal middle post pointer ll payload flag nextPointer nextLl nextPayload (entry.arena.of_metadata countFrame.1) value returnRun
    exact ⟨same,(Frame.of_readonly returnFrame).trans ⟨countFrame.1,countFrame.2⟩,fun impossible=>(zero impossible).elim⟩

theorem after_read_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length ll payload flag : BitVec 64)
    (entry : Entry source pointer length) (small : ll.toNat≤8) (room : 1+ll.toNat≤length.toNat)
    (binary : flag=0#64 ∨ flag=1#64)
    (llCell : source.locals.lookup (ofString "ll")=some (.val (.word ll)))
    (payloadCell : source.locals.lookup (ofString "n")=some (.val (.word payload)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (afterRead flag)=(some (.returned value),post)) :
    Valid pointer length.toNat value ∧ Frame source post ∧
      (flag=0#64 → Input.LocalEffects.erase post=Input.LocalEffects.erase source) ∧ kindOf value=some flag := by
  obtain ⟨canonicalRun,afterCanonical⟩ := Fail.guard_return source post _ [.const 5#64] _ value installed normal
  have leftRead : eval source (.op .sub [.op .sub [localVar "len",.const 1#64],localVar "ll"])=some (.val (.word (length-1#64-ll))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,entry.lengthCell,llCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have rightRead : eval source (localVar "n")=some (.val (.word payload)) := by simp [eval,evalHOLExact,localVar,toExact,payloadCell]
  obtain ⟨bound,tailRun⟩ := Fail.lower_guard_return source post _ _ (length-1#64-ll) payload [.const 3#64] _ value leftRead rightRead installed afterCanonical
  have number1 : (length-1#64).toNat=length.toNat-1 := BitVec.toNat_sub_of_le (by change 1≤length.toNat; exact entry.nonempty)
  have number : (length-1#64-ll).toNat=length.toNat-1-ll.toNat := by
    rw [BitVec.toNat_sub_of_le (by change ll.toNat≤(length-1#64).toNat; rw [number1]; omega),number1]
  rw [number] at bound
  have bounded : 1+ll.toNat+payload.toNat≤length.toNat := by omega
  obtain ⟨same,nextArena,pure⟩ := long_tail_normal source post pointer length ll payload flag entry llCell payloadCell bounded installed value tailRun
  have headerNumber : (1#64+ll).toNat=1+ll.toNat := BitVec.toNat_add_of_lt (by change 1+ll.toNat<2^64; omega)
  refine ⟨⟨1#64+ll,payload,flag,same,?_,?_,?_,binary,?_⟩,nextArena,pure,by rw [same]; rfl⟩
  · rw [headerNumber]; omega
  · rw [headerNumber]; omega
  · rw [headerNumber]; exact bounded
  · intro listFlag; rw [headerNumber]; omega

end InitECandidate.Solver.Rlp.CurrentItem

#print axioms InitECandidate.Solver.Rlp.CurrentItem.long_return_normal
#print axioms InitECandidate.Solver.Rlp.CurrentItem.long_tail_normal
#print axioms InitECandidate.Solver.Rlp.CurrentItem.after_read_normal
