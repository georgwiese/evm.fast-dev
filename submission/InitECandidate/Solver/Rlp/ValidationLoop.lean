import InitECandidate.Solver.Rlp.ValidationParse
import InitECandidate.Solver.Rlp.ValidationAtEnd
import InitECandidate.Solver.Input.ClockCostCurrentLoop

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem loop_body_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rootEnd cursor limit position ending : BitVec 64) (frames : List Frame)
    (view : View source rootEnd cursor limit position ending 1#64 frames)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source loopBody=(none,target)) :
    Invariant rootEnd limit target ∧ currentRank rootEnd target<currentRank rootEnd source := by
  have dispatch : evaluateHOLFiniteState source loopBody=
      if position=ending then evaluateHOLFiniteState source atEnd else evaluateHOLFiniteState source parse := by
    simp [loop_body_shape,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,view.positionCell,view.endCell,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [dispatch] at normal
  by_cases same : position=ending
  · rw [if_pos same] at normal
    exact at_end_none source target rootEnd cursor limit position ending frames view same normal
  · rw [if_neg same] at normal
    exact parse_none source target rootEnd cursor limit position ending frames view installed normal

theorem condition_active (source : PanSemStateFiniteExact 64 Guest.HostMemory) (go word : BitVec 64)
    (goCell : source.locals.lookup (ofString "go")=some (.val (.word go))) (binary : go=0#64 ∨ go=1#64)
    (read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) condition=some (.val (.word word)))
    (nonzero : word≠0) : go=1#64 := by
  rcases binary with zero | one
  · rw [zero] at goCell
    have observed : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) condition=some (.val (.word 0#64)) := by
      simp [evalHOLFinite,condition,evalHOLExact,localVar,toExact,goCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have same : word=0#64 := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (read.symm.trans observed)))
    exact (nonzero same).elim
  · exact one

/-- An instantiated bound for the unchanged nested validator loop. Every
outcome is priced; successful bodies preserve the actual linked-record
invariant and strictly decrease its uniquely determined physical rank. -/
theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (rootEnd limit : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code) (valid : Invariant rootEnd limit source) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤14*currentRank rootEnd source := by
  rw [loop_shape]
  apply Input.ClockCost.ranked_loop_current source.code condition loopBody 13 (Invariant rootEnd limit) (currentRank rootEnd) ?_ ?_ source rfl valid
  · intro current codeEq model word read nonzero positive
    obtain ⟨cursor,position,ending,go,frames,view⟩ := model
    exact loop_body_cost (decClockHOLFinite current) position ending view.positionCell view.endCell (by change Input.OriginalCode.Installed current.code; rw [codeEq]; exact installed)
  · intro current codeEq model word read nonzero
    obtain ⟨cursor,position,ending,go,frames,view⟩ := model
    have active := condition_active current go word view.goCell view.binary read nonzero
    subst go
    refine ⟨?_,?_⟩
    · rw [View.rank_eq _ _ _ _ _ _ _ _ view]
      change 0<2*(rootEnd.toNat-position.toNat)+frames.length+1
      omega
    · intro positive
      dsimp only
      intro continuing
      have noContinue := (loop_body_prefix.summary_full (decClockHOLFinite current)).2.2.2
      have actualNone : (evaluateHOLFiniteState (decClockHOLFinite current) loopBody).1=none := continuing.resolve_right noContinue
      have currentView := View.clock current rootEnd cursor limit position ending 1#64 frames (current.clock-1) view
      have transition := loop_body_none (decClockHOLFinite current) (evaluateHOLFiniteState (decClockHOLFinite current) loopBody).2
        rootEnd cursor limit position ending frames currentView
        (by change Input.OriginalCode.Installed current.code; rw [codeEq]; exact installed) (Prod.ext actualNone rfl)
      refine ⟨transition.1,?_⟩
      have sameRank : currentRank rootEnd (decClockHOLFinite current)=currentRank rootEnd current :=
        (View.rank_eq _ _ _ _ _ _ _ _ currentView).trans (View.rank_eq _ _ _ _ _ _ _ _ view).symm
      exact transition.2.trans_eq sameRank

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.loop_body_none
#print axioms InitECandidate.Solver.Rlp.Validation.condition_active
#print axioms InitECandidate.Solver.Rlp.Validation.loop_cost
