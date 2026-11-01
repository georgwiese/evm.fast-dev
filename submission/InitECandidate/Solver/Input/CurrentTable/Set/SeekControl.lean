import InitECandidate.Solver.Input.CurrentTable.Set.SeekLoop
import InitECandidate.Solver.Input.ReturnFactsLoop
import InitECandidate.Solver.Input.NoReturnDecision

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original insertion step has no return on any input. -/
theorem seek_step_never_any : NoReturn.Never seekStep := by
  rw [seek_shapes.2.2.1,seek_shapes.2.2.2]
  apply NoReturn.declared
  apply NoReturn.sequence
  · exact NoReturn.conditional _ _ _ NoReturn.breaks NoReturn.skip
  · apply NoReturn.sequence
    · intro F source value
      have safe : LocalPrefix (ofString "_") setParent:=by
        rw [setParent]
        exact .assign _ _ (by decide)
      exact (safe.summary_full source).2.1 value
    · intro F source value
      exact (FindLeaf.branch_safe.summary_full source).2.1 value

/-- No caller return escapes the actual insertion loop, independently of
any table image or future successful search. -/
theorem seek_never_any (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    ∀ value,(evaluateHOLFiniteState source seek).1≠some (.returned value) := by
  have returns:=ReturnFacts.loop source.code FindLeaf.test seekStep (fun _=>True) (fun _=>False)
    (by intro current codeEq state observed read nonzero funded target value run
        exact seek_step_never_any _ value (congrArg Prod.fst run))
    (by intro current codeEq state observed read nonzero funded target result run continuing
        trivial) source rfl True.intro
  intro value observed
  rw [seek_shapes.2.1] at observed
  exact returns _ value (Prod.ext observed rfl)

/-- This actual mapped insertion search cannot return from htab_set. Only
its real subsequent leaf/internal-call continuation can supply that return. -/
theorem seek_never {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base root leaf pointer : BitVec 64} {difference : Nat} {valid : BitVec 64 → Prop}
    {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64} {keys : BitVec 64 → KeyBits.Key} {query : KeyBits.Key}
    (image : FindLeaf.Nodes origin base valid bits left right) (model : Routing valid bits left right keys)
    (ready : Seeking origin source base root leaf pointer difference valid bits left right query)
    (marked : bits leaf = 256) (differenceBound : difference ≤ 256) (view : FirstDiff.ByteView origin pointer query) :
    ∀ value,(evaluateHOLFiniteState source seek).1 ≠ some (.returned value) := seek_never_any source

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.seek_never

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.seek_step_never_any
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.seek_never_any
