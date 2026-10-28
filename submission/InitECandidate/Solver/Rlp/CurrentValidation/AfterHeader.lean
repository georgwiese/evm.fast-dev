import InitECandidate.Solver.Rlp.CurrentValidation.Push
import InitECandidate.Solver.Input.NoneControl
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Rlp.CurrentValidation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

theorem choose_evaluate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (header payload flag : BitVec 64)
    (cell : source.locals.lookup (ofString "h")=some (Header.result header payload flag)) :
    evaluateHOLFiniteState source Validation.choose=
      if flag≠0#64 then evaluateHOLFiniteState source Validation.push else evaluateHOLFiniteState source Validation.move := by
  simp [Validation.choose,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,cell,Header.result,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-- A real continuing choice must be a flat item. A nested item fails at
its first actual scratch store, so no mapped-stack premise is needed. -/
theorem choose_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (position ending header payload flag : BitVec 64) (data : State source position ending 1#64)
    (hCell : source.locals.lookup (ofString "h")=some (Header.result header payload flag))
    (afterCell : source.locals.lookup (ofString "after")=some (.val (.word (position+header+payload))))
    (positive : 1≤header.toNat+payload.toNat) (extent : header.toNat+payload.toNat≤(ending-position).toNat)
    (normal : evaluateHOLFiniteState source Validation.choose=(none,target)) :
    ∃ next,State target next ending 1#64 ∧ position.toNat<next.toNat := by
  rw [choose_evaluate source header payload flag hCell] at normal
  by_cases zero : flag=0#64
  · rw [if_neg (not_not_intro zero)] at normal
    have remaining : (ending-position).toNat=ending.toNat-position.toNat := BitVec.toNat_sub_of_le (show position≤ending from data.ordered)
    rw [remaining] at extent
    have firstNumber : (position+header).toNat=position.toNat+header.toNat :=
      BitVec.toNat_add_of_lt (by have h:=ending.isLt; omega)
    have nextNumber : (position+header+payload).toNat=position.toNat+header.toNat+payload.toNat := by
      rw [BitVec.toNat_add_of_lt (by rw [firstNumber]; have h:=ending.isLt; omega),firstNumber]
    have read : eval source (localVar "after")=some (.val (.word (position+header+payload))) := by
      simp [eval,evalHOLExact,localVar,toExact,afterCell]
    have assigned:=StateSteps.assign_execute source "pos" (localVar "after") position (position+header+payload) data.positionCell read
    change evaluateHOLFiniteState source Validation.move=(none,bind source "pos" (position+header+payload)) at assigned
    have same : target=bind source "pos" (position+header+payload) := (Prod.mk.inj (normal.symm.trans assigned)).2
    rw [same]
    exact ⟨position+header+payload,data.moved _ (by rw [nextNumber]; omega),by rw [nextNumber]; omega⟩
  · rw [if_pos zero] at normal
    exact False.elim (push_not_none source target data.arena (position+header+payload) afterCell normal)

/-- Actual payload/after declarations, choice and lexical restoration retain
the flat current parse and advance its real input position on continuation. -/
theorem after_header_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (position ending header payload flag : BitVec 64) (data : State source position ending 1#64)
    (hCell : source.locals.lookup (ofString "h")=some (Header.result header payload flag))
    (positive : 1≤header.toNat+payload.toNat) (extent : header.toNat+payload.toNat≤(ending-position).toNat)
    (normal : evaluateHOLFiniteState source Validation.afterHeader=(none,target)) :
    ∃ next,State target next ending 1#64 ∧ position.toNat<next.toNat := by
  have payloadRead : eval source (.op .add [localVar "pos",.rfield 0 (localVar "h")])=some (.val (.word (position+header))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,data.positionCell,hCell,Header.result,valueIsWord,valueWord,wordOpHOL,wordOp]
  unfold Validation.afterHeader at normal
  obtain ⟨payloadInner,payloadRun,payloadRestore⟩ := declaration_none source target "payload" _ (position+header) _ payloadRead normal
  let payloadState:=bind source "payload" (position+header)
  have payloadData : State payloadState position ending 1#64 := data.bound_value "payload" (.val (.word (position+header))) (by decide)
  have payloadHeader : payloadState.locals.lookup (ofString "h")=some (Header.result header payload flag) :=
    (bind_lookup_other source "payload" "h" (position+header) (by decide)).trans hCell
  have payloadCell : payloadState.locals.lookup (ofString "payload")=some (.val (.word (position+header))) := bind_lookup_same source "payload" (position+header)
  have afterRead : eval payloadState (.op .add [localVar "payload",.rfield 1 (localVar "h")])=some (.val (.word (position+header+payload))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,payloadCell,payloadHeader,Header.result,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨afterInner,afterRun,afterRestore⟩ := declaration_none payloadState payloadInner "after" _ (position+header+payload) Validation.choose afterRead payloadRun
  let afterState:=bind payloadState "after" (position+header+payload)
  have afterData : State afterState position ending 1#64 := payloadData.bound_value "after" (.val (.word (position+header+payload))) (by decide)
  have afterHeader : afterState.locals.lookup (ofString "h")=some (Header.result header payload flag) :=
    (bind_lookup_other payloadState "after" "h" (position+header+payload) (by decide)).trans payloadHeader
  have afterCell : afterState.locals.lookup (ofString "after")=some (.val (.word (position+header+payload))) := bind_lookup_same payloadState "after" (position+header+payload)
  obtain ⟨next,nextData,advances⟩ := choose_none afterState afterInner position ending header payload flag afterData afterHeader afterCell positive extent afterRun
  have first:=nextData.restored payloadState "after" (by decide)
  rw [←afterRestore] at first
  have final:=first.restored source "payload" (by decide)
  rw [←payloadRestore] at final
  exact ⟨next,final,advances⟩

end InitECandidate.Solver.Rlp.CurrentValidation

#print axioms InitECandidate.Solver.Rlp.CurrentValidation.choose_none
#print axioms InitECandidate.Solver.Rlp.CurrentValidation.after_header_none
