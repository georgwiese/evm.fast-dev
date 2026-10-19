import InitECandidate.Solver.Rlp.ItemTotal
import InitECandidate.Solver.Rlp.ValidationCallNormal

namespace InitECandidate.Solver.Rlp.ItemTotal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem check_safe : Input.LocalPrefix (ofString "h") check :=
  .ite _ (.call none _ _ (by simp)) .skip

theorem after_header_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload flag cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (headerCell : source.locals.lookup (ofString "h")=some (Header.result header payload flag))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+header.toNat+payload.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterHeader=(some (.returned value),target)) :
    value=.val (.word (header+payload)) ∧ Validation.Arena target cursor limit := by
  obtain ⟨middle,checkRun,returnRun⟩ := Input.sequence_returned source target check (.return total) value (check_safe.summary_full source).2.1 normal
  have next : middle.locals=source.locals ∧ Validation.Arena middle cursor limit := by
    rw [check_evaluate source header payload flag headerCell] at checkRun
    by_cases zero : flag=0#64
    · rw [if_neg (not_not_intro zero),evaluateHOLFiniteState_skip] at checkRun
      have same : middle=source := (Prod.mk.inj checkRun).2.symm
      rw [same]
      exact ⟨rfl,arena⟩
    · rw [if_pos zero] at checkRun
      have number : (pointer+header).toNat=pointer.toNat+header.toNat := BitVec.toNat_add_of_lt (by omega)
      have actual := Validate.ignored_normal source middle (pointer+header) payload cursor limit payloadArguments
        (payload_arguments source pointer header payload flag pointerCell headerCell) arena (by rw [number]; exact fits) installed checkRun
      exact ⟨actual.2.1,actual.2.2.1⟩
  obtain ⟨read,returned⟩ := Input.return_normal middle target total value returnRun
  have currentHeader : middle.locals.lookup (ofString "h")=some (Header.result header payload flag) := by rw [next.1]; exact headerCell
  have totalRead : eval middle total=some (.val (.word (header+payload))) := by
    simp [eval,total,evalHOLExact,evalListHOLExact,localVar,toExact,currentHeader,Header.result,valueIsWord,valueWord,wordOpHOL,wordOp]
  refine ⟨(Option.some.inj (read.symm.trans totalRead)),Validation.Arena.of_fields middle target cursor limit next.2 ?_ ?_⟩
  · rw [returned]
    rfl
  · rw [returned]
    rfl

/-- Actual normal item totals are positive and bounded by the passed
remaining length. The returned total also bounds this body's observed cost,
which permits linear amortization across a real list traversal. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ totalWord : BitVec 64,value=.val (.word totalWord) ∧ 1≤totalWord.toNat ∧ totalWord.toNat≤length.toNat ∧
      Validation.Arena target cursor limit ∧ source.clock-target.clock≤28*totalWord.toNat+30 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length) := by
    simp [arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  obtain ⟨paid,answer,inner,minimum,maximum,funded,valid,continuation,restored⟩ := Header.scoped_normal source target pointer length "h" arguments afterHeader args installed value (by rw [←body_shape]; exact normal)
  obtain ⟨header,payload,flag,same,small,positive,extent,binary,listHeader⟩ := valid
  rw [same] at continuation
  let ready := setVarHOLFinite (ofString "h") (Header.result header payload flag) {source with clock:=source.clock-paid}
  have readyPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)) := by
    simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "h"≠ofString "p" from by decide] using pointerCell
  have readyHeader : ready.locals.lookup (ofString "h")=some (Header.result header payload flag) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have readyArena := Validation.Arena.of_fields source ready cursor limit arena rfl rfl
  have subFits : pointer.toNat+header.toNat+payload.toNat<2^64 := by omega
  obtain ⟨valueEq,nextArena⟩ := after_header_normal ready inner pointer header payload flag cursor limit readyPointer readyHeader readyArena subFits installed value continuation
  have number : (header+payload).toNat=header.toNat+payload.toNat := BitVec.toNat_add_of_lt (by omega)
  have priced := after_header_cost ready pointer header payload flag cursor limit readyPointer readyHeader readyArena subFits installed
  rw [continuation] at priced
  have clock := evaluateHOLFiniteState_clock_le ready afterHeader
  rw [continuation] at clock
  change inner.clock≤source.clock-paid at clock
  change source.clock-paid-inner.clock≤14*(2*payload.toNat+1)+5 at priced
  have postClock : target.clock=inner.clock := by rw [restored]; rfl
  refine ⟨header+payload,valueEq,by rw [number]; exact positive,by rw [number]; exact extent,
    Validation.Arena.of_fields inner target cursor limit nextArena ?_ ?_,?_⟩
  · rw [restored]
    rfl
  · rw [restored]
    rfl
  · rw [postClock,number]
    omega

end InitECandidate.Solver.Rlp.ItemTotal

#print axioms InitECandidate.Solver.Rlp.ItemTotal.check_safe
#print axioms InitECandidate.Solver.Rlp.ItemTotal.after_header_normal
#print axioms InitECandidate.Solver.Rlp.ItemTotal.body_normal
