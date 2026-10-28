import InitECandidate.Solver.Input.CurrentTable.Set.SeekLoop
import InitECandidate.Solver.Input.ReturnFactsLoop

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- This actual mapped insertion search cannot return from htab_set. Only
its real subsequent leaf/internal-call continuation can supply that return. -/
theorem seek_never {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base root leaf pointer : BitVec 64} {difference : Nat} {valid : BitVec 64 → Prop}
    {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64} {keys : BitVec 64 → KeyBits.Key} {query : KeyBits.Key}
    (image : FindLeaf.Nodes origin base valid bits left right) (model : Routing valid bits left right keys)
    (ready : Seeking origin source base root leaf pointer difference valid bits left right query)
    (marked : bits leaf = 256) (differenceBound : difference ≤ 256) (view : FirstDiff.ByteView origin pointer query) :
    ∀ value,(evaluateHOLFiniteState source seek).1 ≠ some (.returned value) := by
  have returns := ReturnFacts.loop source.code FindLeaf.test seekStep
    (fun current => Seeking origin current base root leaf pointer difference valid bits left right query) (fun _ => False)
    (by
      intro current installed state observed actual nonzero funded target value run
      obtain ⟨node,parent,live,member,route,parentLink⟩ := state
      have stepRun := step_execute image live.at_tick member differenceBound query (view.of_frame live.cursor.at_tick.frame)
      rw [stepRun] at run
      split at run <;> cases run)
    (by
      intro current installed state observed actual nonzero funded target result run continuing
      exact (seek_progress image model state marked differenceBound view result run continuing).1)
    source rfl ready
  rw [←seek_shapes.2.1] at returns
  intro value read
  exact returns _ value (Prod.ext read rfl)

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.seek_never
