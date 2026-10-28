import InitECandidate.Solver.Rlp.CurrentValidation.Step
import InitECandidate.Solver.Input.ClockCostCurrentLoop

namespace InitECandidate.Solver.Rlp.CurrentValidation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

def wordAt (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) : BitVec 64 :=
  match source.locals.lookup (ofString name) with | some (.val (.word word))=>word | _=>0#64
def currentRank (ending : BitVec 64) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat :=
  ending.toNat-(wordAt source "pos").toNat+(wordAt source "go").toNat
def Invariant (ending : BitVec 64) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop := ∃ position go,State source position ending go

theorem State.rank_eq {source : PanSemStateFiniteExact 64 Guest.HostMemory} {position ending go : BitVec 64}
    (data : State source position ending go) : currentRank ending source=ending.toNat-position.toNat+go.toNat := by
  simp only [currentRank,wordAt,data.positionCell,data.goCell]

theorem State.condition_active {source : PanSemStateFiniteExact 64 Guest.HostMemory} {position ending go : BitVec 64}
    (data : State source position ending go) (word : BitVec 64)
    (read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) Validation.condition=some (.val (.word word)))
    (nonzero : word≠0) : go=1#64 := by
  rcases data.binary with zero|one
  · have cell:=data.goCell
    rw [zero] at cell
    have observed : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) Validation.condition=some (.val (.word 0#64)) := by
      simp [evalHOLFinite,Validation.condition,evalHOLExact,localVar,toExact,cell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have same : word=0#64 := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (read.symm.trans observed)))
    exact False.elim (nonzero same)
  · exact one

/-- Whole actual internal validator loop with the current below-domain
scratch state. Every continuing body consumes input or finishes; nested pushes
are priced before they fail. All outcomes and exhausted clocks are included. -/
theorem loop_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (position ending go : BitVec 64)
    (data : State source position ending go) :
    source.clock-(evaluateHOLFiniteState source Validation.loop).2.clock≤14*(ending.toNat-position.toNat+go.toNat) := by
  rw [←data.rank_eq,Validation.loop_shape]
  apply ClockCost.ranked_loop_current source.code Validation.condition Validation.loopBody 13 (Invariant ending) (currentRank ending) ?_ ?_ source rfl ⟨position,go,data⟩
  · intro current codeEq model word read nonzero funded
    obtain ⟨position,go,data⟩ := model
    exact Validation.loop_body_cost (decClockHOLFinite current) position ending data.positionCell data.endCell data.arena.code
  · intro current codeEq model word read nonzero
    obtain ⟨position,go,data⟩ := model
    have active:=data.condition_active word read nonzero
    subst go
    refine ⟨?_,?_⟩
    · rw [data.rank_eq]
      change 0<ending.toNat-position.toNat+1
      omega
    · intro funded
      dsimp only
      intro continuing
      have noContinue:=(Validation.loop_body_prefix.summary_full (decClockHOLFinite current)).2.2.2
      have actualNone : (evaluateHOLFiniteState (decClockHOLFinite current) Validation.loopBody).1=none := continuing.resolve_right noContinue
      have currentData:=data.at_clock (current.clock-1)
      obtain ⟨next,nextGo,nextData,smaller,frame⟩ := loop_body_none (decClockHOLFinite current) (evaluateHOLFiniteState (decClockHOLFinite current) Validation.loopBody).2
        position ending currentData (Prod.ext actualNone rfl)
      refine ⟨⟨next,nextGo,nextData⟩,?_⟩
      rw [nextData.rank_eq,data.rank_eq]
      exact smaller

end InitECandidate.Solver.Rlp.CurrentValidation

#print axioms InitECandidate.Solver.Rlp.CurrentValidation.loop_cost
