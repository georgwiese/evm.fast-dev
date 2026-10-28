import InitECandidate.Solver.Input.CurrentTable.Set.SeekLoop

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- A real normal insertion search retains every caller binding other
than its actual n/p assignments. The temporary b declaration is restored. -/
theorem seek_local {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base root leaf pointer : BitVec 64} {difference : Nat} {valid : BitVec 64 → Prop}
    {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64} {keys : BitVec 64 → KeyBits.Key} {query : KeyBits.Key}
    (image : FindLeaf.Nodes origin base valid bits left right) (model : Routing valid bits left right keys)
    (ready : Seeking origin source base root leaf pointer difference valid bits left right query)
    (marked : bits leaf = 256) (differenceBound : difference ≤ 256) (view : FirstDiff.ByteView origin pointer query)
    (name : String) (notParent : ofString "p" ≠ ofString name) (notNode : ofString "n" ≠ ofString name)
    (normal : evaluateHOLFiniteState source seek = (none,post)) :
    post.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
  rw [seek_shapes.2.1] at normal
  apply loop_control_exit FindLeaf.test seekStep
    (fun current => Seeking origin current base root leaf pointer difference valid bits left right query ∧
      current.locals.lookup (ofString name) = source.locals.lookup (ofString name))
    (fun current => current.locals.lookup (ofString name) = source.locals.lookup (ofString name)) _ _ _ source post ⟨ready,rfl⟩ normal
  · intro current validState stopped
    exact validState.2
  · intro current validState observed actual nonzero funded target result run continuing
    have next := (seek_progress image model validState.1 marked differenceBound view result run continuing).1
    obtain ⟨node,parent,live,member,route,parentLink⟩ := validState.1
    have stepRun := step_execute image live.at_tick member differenceBound query (view.of_frame live.cursor.at_tick.frame)
    by_cases stopped : difference ≤ bits node
    · rw [if_pos stopped] at stepRun
      rw [stepRun] at run
      have resultEq := congrArg Prod.fst run
      dsimp only at resultEq
      rw [←resultEq] at continuing
      simp at continuing
    · rw [if_neg stopped] at stepRun
      rw [stepRun] at run
      have endpoint := congrArg Prod.snd run
      dsimp only at endpoint
      refine ⟨next,?_⟩
      rw [←endpoint]
      exact (bind_lookup_other (bind (decClockHOLFinite current) "p" node) "n" name _ notNode).trans
        ((bind_lookup_other (decClockHOLFinite current) "p" name node notParent).trans validState.2)
  · intro current validState observed actual nonzero funded target run
    obtain ⟨node,parent,live,member,route,parentLink⟩ := validState.1
    have stepRun := step_execute image live.at_tick member differenceBound query (view.of_frame live.cursor.at_tick.frame)
    by_cases stopped : difference ≤ bits node
    · rw [if_pos stopped] at stepRun
      rw [stepRun] at run
      have endpoint := congrArg Prod.snd run
      dsimp only at endpoint
      rw [←endpoint]
      exact validState.2
    · rw [if_neg stopped] at stepRun
      rw [stepRun] at run
      cases run

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.seek_local
