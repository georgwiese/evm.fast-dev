import InitECandidate.Solver.Rlp.CurrentItemTotalCost
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.ReturnNormal
import InitECandidate.Solver.Input.IgnoredCallLookup

namespace InitECandidate.Solver.Rlp.CurrentItemTotal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

theorem check_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer header payload flag : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (headerCell : source.locals.lookup (ofString "h")=some (Header.result header payload flag))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+header.toNat+payload.toNat<2^64)
    (normal : evaluateHOLFiniteState source ItemTotal.check=(none,post)) :
    post.locals=source.locals ∧ LocalEffects.erase post=LocalEffects.erase source := by
  rw [ItemTotal.check_evaluate source header payload flag headerCell] at normal
  by_cases zero : flag=0#64
  · rw [if_neg (not_not_intro zero),evaluateHOLFiniteState_skip] at normal
    have same : post=source := (congrArg Prod.snd normal).symm
    rw [same]
    exact ⟨rfl,rfl⟩
  · rw [if_pos zero] at normal
    have number : (pointer+header).toNat=pointer.toNat+header.toNat := BitVec.toNat_add_of_lt (by omega)
    have frame:=CurrentValidate.ignored_frame source post (pointer+header) payload arena (by rw [number]; exact fits) ItemTotal.payloadArguments
      (ItemTotal.payload_arguments source pointer header payload flag pointerCell headerCell) normal
    have locals : post.locals=source.locals := by
      apply HolFiniteMapExact.ext
      funext name
      exact CallNormal.ignored_lookup source post name (ofString "rlp_validate_items") ItemTotal.payloadArguments normal
    exact ⟨locals,frame⟩

/-- A real normal item-total return derives its positive nonwrapping byte
advance, complete nonlocal frame and cost at the bytes actually consumed.
This allows a list to share one byte budget across all real iterations. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source ItemTotal.body=(some (.returned value),post)) :
    ∃ word : BitVec 64,value=.val (.word word) ∧ 1≤word.toNat ∧ word.toNat≤length.toNat ∧
      LocalEffects.erase post=LocalEffects.erase source ∧ source.clock-post.clock≤14*word.toNat+30 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) ItemTotal.arguments=some (Header.values pointer length) := by
    simp [ItemTotal.arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  rw [ItemTotal.body_shape] at normal
  obtain ⟨paid,answer,inner,minimum,maximum,funded,valid,remaining,endpoint⟩ := Header.scoped_normal source post pointer length "h" ItemTotal.arguments ItemTotal.afterHeader args arena.code value normal
  obtain ⟨header,payload,flag,valueEq,headerBound,positive,extent,binary,listHeader⟩ := valid
  subst answer
  let entry:=setVarHOLFinite (ofString "h") (Header.result header payload flag) {source with clock:=source.clock-paid}
  have entryPointer : entry.locals.lookup (ofString "p")=some (.val (.word pointer)) := by
    simpa [entry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "h"≠ofString "p" from by decide] using pointerCell
  have entryHeader : entry.locals.lookup (ofString "h")=some (Header.result header payload flag) := by
    simp [entry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have entryArena : CurrentStartup.ArenaState entry := arena.of_frame rfl
  have safe : LocalPrefix (ofString "p") ItemTotal.check := by
    unfold ItemTotal.check ItemTotal.validate
    exact .ite _ (.call none _ _ (by intro name impossible; cases impossible)) .skip
  obtain ⟨middle,checkRun,returnRun⟩ := sequence_returned entry inner ItemTotal.check (.return ItemTotal.total) value (safe.summary_full entry).2.1 remaining
  obtain ⟨locals,frame⟩ := check_frame entry middle pointer header payload flag entryPointer entryHeader entryArena (by omega) checkRun
  have middleHeader : middle.locals.lookup (ofString "h")=some (Header.result header payload flag) := by rw [locals]; exact entryHeader
  have totalRead : eval middle ItemTotal.total=some (.val (.word (header+payload))) := by
    simp [eval,evalHOLExact,evalListHOLExact,ItemTotal.total,localVar,toExact,middleHeader,Header.result,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨read,returned⟩ := return_normal middle inner ItemTotal.total value returnRun
  have valueWord : value=.val (.word (header+payload)) := Option.some.inj (read.symm.trans totalRead)
  have number : (header+payload).toNat=header.toNat+payload.toNat := BitVec.toNat_add_of_lt (by have h:=length.isLt; omega)
  have price:=after_header_cost entry pointer header payload flag entryPointer entryHeader entryArena (by omega)
  rw [remaining] at price
  change source.clock-paid-inner.clock≤14*(payload.toNat+1)+5 at price
  have forward:=evaluateHOLFiniteState_clock_le entry ItemTotal.afterHeader
  rw [remaining] at forward
  change inner.clock≤source.clock-paid at forward
  refine ⟨header+payload,valueWord,(by rw [number]; exact positive),(by rw [number]; exact extent),?_,?_⟩
  · rw [endpoint,returned]
    exact frame
  · rw [endpoint]
    change source.clock-inner.clock≤14*(header+payload).toNat+30
    rw [number]
    omega

end InitECandidate.Solver.Rlp.CurrentItemTotal

#print axioms InitECandidate.Solver.Rlp.CurrentItemTotal.check_frame
#print axioms InitECandidate.Solver.Rlp.CurrentItemTotal.body_normal
