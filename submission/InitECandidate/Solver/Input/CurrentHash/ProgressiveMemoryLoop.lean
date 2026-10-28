import InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryStep

namespace InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryLoop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open Progressive ProgressiveRound

/-- The same complete normal geometric loop retains memory/current heap and
derives the actual terminal round used by the following fold. -/
theorem frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots cursor zeros query : BitVec 64) (n k : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : Round source p roots n k)
    (bounded : n≤134217728) (round : k≤15)
    (inputArena : AllocatedBytes.Arena p (32*n)) (rootsArena : AllocatedBytes.Arena roots 768) (rootsAway : CopyGeneral.Away roots query 768)
    (actual : evaluateHOLFiniteState source loop=(none,post)) :
    post.memory query=source.memory query ∧ MerkleMemory.Context post cursor zeros query ∧
      ∃ position, position≤15 ∧ Round post p roots n position := by
  let invariant (state : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
    MerkleMemory.Context state cursor zeros query ∧ ∃ position, position≤15 ∧ Round state p roots n position ∧ state.memory query=source.memory query
  have final : invariant post := by
    rw [loop_shape.1] at actual
    apply loop_invariant_no_control source.code test step
      (fun current=>((step_other (ofString "n") (by decide) (by decide) (by decide) (by decide)).summary_full current).2.2)
      invariant _ source post rfl ⟨context,k,round,data,rfl⟩ actual
    intro current codeEq ready word read nonzero funded target continued
    obtain ⟨currentContext,position,positionBound,currentData,kept⟩ := ready
    have expected := ProgressiveLoopCost.test_read current p roots n position currentData bounded positionBound
    have active : offset position<n := by
      by_cases active : offset position<n
      · exact active
      rw [if_neg active] at expected
      have zero : word=0#64 := by
        simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
      exact False.elim (nonzero zero)
    have nextBound := active_round n position bounded active
    have image := ProgressiveMemoryStep.frame (decClockHOLFinite current) target p roots cursor zeros query n position
      (currentContext.of_frozen rfl) currentData.dec_clock bounded active inputArena rootsArena rootsAway continued
    have next := ProgressiveRound.step_normal (decClockHOLFinite current) target p roots n position bounded active currentData.dec_clock continued
    exact ⟨image.2,position+1,by omega,next,image.1.trans kept⟩
  obtain ⟨context,position,positionBound,data,kept⟩ := final
  exact ⟨kept,context,position,positionBound,data⟩

end InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryLoop

#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryLoop.frame
