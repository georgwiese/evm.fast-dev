import InitECandidate.Solver.Rlp.ValidationChoose
import InitECandidate.Solver.Input.NoneControl

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_header_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rootEnd cursor limit position ending header payload flag : BitVec 64) (frames : List Frame)
    (view : View source rootEnd cursor limit position ending 1#64 frames)
    (hCell : source.locals.lookup (ofString "h")=some (Header.result header payload flag))
    (positive : 1≤header.toNat+payload.toNat) (extent : header.toNat+payload.toNat≤(ending-position).toNat)
    (binary : flag=0#64 ∨ flag=1#64) (listHeader : flag=1#64 → 1≤header.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source afterHeader=(none,target)) :
    ∃ nextCursor nextPosition nextEnding nextFrames,
      View target rootEnd nextCursor limit nextPosition nextEnding 1#64 nextFrames ∧
      rank rootEnd nextPosition nextFrames.length true<rank rootEnd position frames.length true := by
  have payloadRead : eval source (.op .add [localVar "pos",.rfield 0 (localVar "h")])=some (.val (.word (position+header))) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,view.positionCell,hCell,Header.result,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨payloadInner,payloadRun,payloadRestore⟩ := Input.declaration_none source target "payload" _ (position+header)
    (.dec (ofString "after") .one (.op .add [localVar "payload",.rfield 1 (localVar "h")]) choose) payloadRead normal
  let payloadState := bind source "payload" (position+header)
  have payloadView := View.bound_word source rootEnd cursor limit position ending 1#64 (position+header) frames "payload" view (by decide) (by decide) (by decide) (by decide)
  have payloadHeader : payloadState.locals.lookup (ofString "h")=some (Header.result header payload flag) :=
    (bind_lookup_other _ "payload" "h" _ (by decide)).trans hCell
  have afterRead : eval payloadState (.op .add [localVar "payload",.rfield 1 (localVar "h")])=some (.val (.word (position+header+payload))) := by
    have payloadCurrent := bind_lookup_same source "payload" (position+header)
    change payloadState.locals.lookup (ofString "payload")=_ at payloadCurrent
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,payloadCurrent,payloadHeader,Header.result,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨afterInner,afterRun,afterRestore⟩ := Input.declaration_none payloadState payloadInner "after" _ (position+header+payload) choose afterRead payloadRun
  let afterState := bind payloadState "after" (position+header+payload)
  have afterView := View.bound_word payloadState rootEnd cursor limit position ending 1#64 (position+header+payload) frames "after" payloadView (by decide) (by decide) (by decide) (by decide)
  have afterHeaderCell : afterState.locals.lookup (ofString "h")=some (Header.result header payload flag) :=
    (bind_lookup_other _ "after" "h" _ (by decide)).trans payloadHeader
  have afterPayloadCell : afterState.locals.lookup (ofString "payload")=some (.val (.word (position+header))) :=
    (bind_lookup_other _ "after" "payload" _ (by decide)).trans (bind_lookup_same _ _ _)
  obtain ⟨nextCursor,nextPosition,nextEnding,nextFrames,chosen,smaller⟩ := choose_none afterState afterInner rootEnd cursor limit position ending header payload flag frames afterView afterHeaderCell afterPayloadCell
    (bind_lookup_same _ _ _) positive extent binary listHeader installed afterRun
  have afterRestored := View.restored afterInner payloadState rootEnd nextCursor limit nextPosition nextEnding 1#64 nextFrames "after" chosen (by decide) (by decide) (by decide) (by decide)
  rw [←afterRestore] at afterRestored
  have payloadRestored := View.restored payloadInner source rootEnd nextCursor limit nextPosition nextEnding 1#64 nextFrames "payload" afterRestored (by decide) (by decide) (by decide) (by decide)
  rw [←payloadRestore] at payloadRestored
  exact ⟨nextCursor,nextPosition,nextEnding,nextFrames,payloadRestored,smaller⟩

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.after_header_none
