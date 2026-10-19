import InitECandidate.Solver.Rlp.ValidationAfterHeader
import InitECandidate.Solver.Rlp.ValidationBodyCost

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Compose the actual header call, its actual returned words, the real
string/list continuation and lexical restoration. No future parsed header or
pending-record model is supplied. -/
theorem parse_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rootEnd cursor limit position ending : BitVec 64) (frames : List Frame)
    (view : View source rootEnd cursor limit position ending 1#64 frames)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source parse=(none,target)) :
    Invariant rootEnd limit target ∧ currentRank rootEnd target<currentRank rootEnd source := by
  obtain ⟨paid,answer,inner,minimum,maximum,funded,valid,continuation,restored⟩ :=
    Header.scoped_none source target position (ending-position) "h" headerArguments afterHeader
      (header_arguments source position ending view.positionCell view.endCell) installed normal
  obtain ⟨header,payload,flag,answerEq,small,positive,extent,binary,listHeader⟩ := valid
  rw [answerEq] at continuation
  let ready := setVarHOLFinite (ofString "h") (Header.result header payload flag) {source with clock:=source.clock-paid}
  have localOther (name : String) (other : ofString name≠ofString "h") :
      ready.locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,other,Ne.symm other]
  have readyView : View ready rootEnd cursor limit position ending 1#64 frames :=
    View.of_fields source ready rootEnd cursor limit position ending 1#64 frames view rfl rfl rfl
      ((localOther "pos" (by decide)).trans view.positionCell)
      ((localOther "end" (by decide)).trans view.endCell)
      ((localOther "top" (by decide)).trans view.topCell)
      ((localOther "go" (by decide)).trans view.goCell)
  have headerCell : ready.locals.lookup (ofString "h")=some (Header.result header payload flag) := by
    simp [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  obtain ⟨nextCursor,nextPosition,nextEnding,nextFrames,continued,smaller⟩ :=
    after_header_none ready inner rootEnd cursor limit position ending header payload flag frames readyView headerCell
      positive extent binary listHeader installed continuation
  have postView := View.restored inner source rootEnd nextCursor limit nextPosition nextEnding 1#64 nextFrames "h" continued
    (by decide) (by decide) (by decide) (by decide)
  rw [←restored] at postView
  refine ⟨⟨nextCursor,nextPosition,nextEnding,1#64,nextFrames,postView⟩,?_⟩
  rw [View.rank_eq _ _ _ _ _ _ _ _ postView,View.rank_eq _ _ _ _ _ _ _ _ view]
  exact smaller

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.parse_none
