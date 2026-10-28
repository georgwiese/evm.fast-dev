import InitECandidate.Solver.Input.CurrentTable.Set.SeekEntry
import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Context

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

/-- The genuine post-difference phase either stops within its257tick
allowance or reaches the original new-leaf caller with the real strict
split and parent edge. Neither allocation nor its success is supplied. -/
theorem seek_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table base root leaf pointer : BitVec 64) (difference : Nat)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (keys : BitVec 64 → KeyBits.Key) (query : KeyBits.Key)
    (context : FindLeaf.Context source table base root valid bits left right)
    (model : Routing valid bits left right keys) (rootMember : valid root) (marked : bits leaf = 256)
    (route : Route bits left right query root leaf) (differenceInside : difference < 256)
    (first : KeyBits.First query (keys leaf) difference)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (differenceCell : source.locals.lookup (ofString "d") = some (.val (.word (BitVec.ofNat 64 difference))))
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer)))
    (view : FirstDiff.ByteView source pointer query)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterDifference = (outcome,post)) :
    (source.clock-post.clock ≤ 257 ∧ ∀ value,outcome ≠ some (.returned value)) ∨
      ∃ target inner node parent,SeekState source target base node parent pointer difference ∧ valid node ∧ difference < bits node ∧
        Route bits left right query node leaf ∧ ParentLink valid bits left right query root node parent difference ∧
        target.clock ≤ source.clock ∧ source.clock-target.clock ≤ 257 ∧
        evaluateHOLFiniteState target newLeafCall = (outcome,inner) ∧ post = restoreSeek source base inner := by
  let initial := rootEntry source base root
  have state := initial_state source base root pointer difference differenceCell keyCell
  have ready : Seeking source initial base root leaf pointer difference valid bits left right query :=
    ⟨root,0#64,state,rootMember,route,Or.inl ⟨rfl,rfl⟩⟩
  have price := seek_cost context.image model ready marked (by omega) view
  have never := seek_never context.image model ready marked (by omega) view
  have forward := evaluateHOLFiniteState_clock_le initial seek
  rw [setup_execute source table base root context.domain context.arena context.aligned tableCell context.nodesCell context.rootCell] at run
  change (let output := evaluateHOLFiniteState initial afterNode;(output.1,restoreSeek source base output.2)) = (outcome,post) at run
  rw [seek_shapes.1,evaluateHOLFiniteState_seq_line780] at run
  generalize loopRun : evaluateHOLFiniteState initial seek = output at run price never forward
  obtain ⟨result,target⟩ := output
  change source.clock-target.clock ≤ 257 at price
  change target.clock ≤ source.clock at forward
  cases result with
  | none =>
    have completed : evaluateHOLFiniteState initial seek = (none,target) := loopRun
    obtain ⟨node,parent,state,member,strict,suffix,parentLink⟩ :=
      seek_finished_strict context.image model ready marked differenceInside view first completed
    have observed := congrArg Prod.fst run
    have endpoint := congrArg Prod.snd run
    dsimp only at observed endpoint
    exact Or.inr ⟨target,(evaluateHOLFiniteState target newLeafCall).2,node,parent,state,member,strict,suffix,parentLink,forward,price,
      Prod.ext observed rfl,endpoint.symm⟩
  | some result =>
    have observed := congrArg Prod.fst run
    have endpoint := congrArg Prod.snd run
    dsimp only at observed endpoint
    have clock : post.clock = target.clock := by rw [←endpoint]; rfl
    exact Or.inl ⟨by rw [clock]; exact price,by intro value returned; exact never value (observed.trans returned)⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.seek_trace
