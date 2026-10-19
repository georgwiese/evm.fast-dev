import InitECandidate.Solver.Rlp.ValidationPop
import InitECandidate.Solver.Rlp.ValidationView

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem at_end_evaluate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (top : BitVec 64)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word top))) :
    evaluateHOLFiniteState source atEnd=
      if top=0#64 then evaluateHOLFiniteState source stop else evaluateHOLFiniteState source pop := by
  simp [atEnd,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,topCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-- The real empty-stack stop and nonempty-stack pop both decrease the
current physical rank. Saved positions and links are read from actual memory. -/
theorem at_end_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rootEnd cursor limit position ending : BitVec 64) (frames : List Frame)
    (view : View source rootEnd cursor limit position ending 1#64 frames)
    (atEnd : position=ending) (normal : evaluateHOLFiniteState source Validation.atEnd=(none,target)) :
    Invariant rootEnd limit target ∧ currentRank rootEnd target<currentRank rootEnd source := by
  rw [at_end_evaluate source (topOf frames) view.topCell] at normal
  cases frames with
  | nil =>
    simp only [topOf,if_pos rfl] at normal
    have read : eval source (.const 0#64)=some (.val (.word 0#64)) := rfl
    have assigned := WitnessRadix.StateSteps.assign_execute source "go" (.const 0#64) 1#64 0#64 view.goCell read
    change evaluateHOLFiniteState source stop=(none,bind source "go" 0#64) at assigned
    have same : target=bind source "go" 0#64 := (Prod.mk.inj (normal.symm.trans assigned)).2
    rw [same]
    have postView : View (bind source "go" 0#64) rootEnd cursor limit position ending 0#64 [] :=
      ⟨Arena.of_fields source _ cursor limit view.arena rfl rfl,
        (bind_lookup_other _ "go" "pos" _ (by decide)).trans view.positionCell,
        (bind_lookup_other _ "go" "end" _ (by decide)).trans view.endCell,
        (bind_lookup_other _ "go" "top" _ (by decide)).trans view.topCell,
        bind_lookup_same _ _ _,view.ordered,Or.inl rfl,view.pending⟩
    refine ⟨⟨cursor,position,ending,0#64,[],postView⟩,?_⟩
    rw [View.rank_eq _ _ _ _ _ _ _ _ postView,View.rank_eq _ _ _ _ _ _ _ _ view]
    exact stop_progress rootEnd position
  | cons frame rest =>
    have active : topOf (frame::rest)≠0#64 := view.pending.2.1
    rw [if_neg active] at normal
    have executed := pop_execute source cursor.toNat rootEnd ending position frame rest view.pending view.positionCell view.endCell view.topCell
    have same : target=popPost source frame rest := (Prod.mk.inj (normal.symm.trans executed)).2
    rw [same]
    have postView : View (popPost source frame rest) rootEnd cursor limit frame.resume frame.parentEnd 1#64 rest :=
      ⟨Arena.of_fields source _ cursor limit view.arena rfl rfl,
        pop_position _ _ _,pop_end _ _ _,pop_top _ _ _,(pop_go _ _ _).trans view.goCell,
        view.pending.2.2.2.2.1,Or.inr rfl,pop_pending source cursor.toNat rootEnd ending frame rest view.pending⟩
    refine ⟨⟨cursor,frame.resume,frame.parentEnd,1#64,rest,postView⟩,?_⟩
    rw [View.rank_eq _ _ _ _ _ _ _ _ postView,View.rank_eq _ _ _ _ _ _ _ _ view]
    have positionEq : position=frame.resume := atEnd.trans view.pending.1
    rw [positionEq]
    exact pop_progress rootEnd frame.resume rest.length

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.at_end_evaluate
#print axioms InitECandidate.Solver.Rlp.Validation.at_end_none
