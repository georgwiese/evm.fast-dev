import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Route
import InitECandidate.Solver.Input.WordPairEnvironment
import InitECandidate.Solver.Input.ScopedCallClassified

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real lookup caller exposes the route to its actual returned leaf.
The insertion continuation may use this earlier route; no successful future
lookup, guessed leaf or independently supplied terminal state is assumed. -/
theorem scoped_route_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table pointer base root : BitVec 64) (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat)
    (left right : BitVec 64 → BitVec 64) (keys : BitVec 64 → KeyBits.Key) (query : KeyBits.Key)
    (context : Context source table base root valid bits left right) (model : Routing valid bits left right keys)
    (rootMember : valid root) (view : FirstDiff.ByteView source pointer query)
    (installed : OriginalCode.Installed source.code)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address => Classical.propDecidable (source.memaddrs address)) expressions =
      some [.val (.word table),.val (.word pointer)])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_find_leaf") expressions continuation) = (outcome,post)) :
    (source.clock-post.clock ≤ 258 ∧ ∀ value,outcome ≠ some (.returned value)) ∨
      ∃ target leaf inner,valid leaf ∧ bits leaf = 256 ∧ Route bits left right query root leaf ∧
        LocalEffects.erase target = LocalEffects.erase source ∧
        target.clock ≤ source.clock ∧ source.clock-target.clock ≤ 258 ∧
        evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word leaf))) continuation = (outcome,inner) ∧
        post = restore source name inner := by
  obtain ⟨callee,called,tableCell,keyCell⟩ := word_pair_environment source.code.lookup
    (ofString "htab_find_leaf") (ofString "t") (ofString "key") body .one table pointer (by decide) (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have ready : Context entry table base root valid bits left right := context.of_frame rfl
  rcases CallNormal.scoped_classified source post name .one (ofString "htab_find_leaf") expressions _ body continuation callee .one 257
    args called (ready.price tableCell) outcome run with stopped | reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩ := reached
    obtain ⟨leaf,answer,member,marked,route,frame⟩ := ready.returned_route model rootMember tableCell keyCell (view.of_frame rfl) value bodyRun
    rw [answer] at continued
    exact Or.inr ⟨target,leaf,inner,member,marked,route,frame,forward,cost,continued,endpoint⟩

theorem scoped_route_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (table pointer base root : BitVec 64) (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat)
    (left right : BitVec 64 → BitVec 64) (keys : BitVec 64 → KeyBits.Key) (query : KeyBits.Key)
    (context : Context source table base root valid bits left right) (model : Routing valid bits left right keys)
    (rootMember : valid root) (view : FirstDiff.ByteView source pointer query)
    (installed : OriginalCode.Installed source.code)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address => Classical.propDecidable (source.memaddrs address)) expressions =
      some [.val (.word table),.val (.word pointer)])
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "htab_find_leaf") expressions continuation) = (some (.returned value),post)) :
    ∃ target leaf inner,valid leaf ∧ bits leaf = 256 ∧ Route bits left right query root leaf ∧
      LocalEffects.erase target = LocalEffects.erase source ∧
      target.clock ≤ source.clock ∧ source.clock-target.clock ≤ 258 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word leaf))) continuation = (some (.returned value),inner) ∧
      post = restore source name inner := by
  rcases scoped_route_trace source post table pointer base root valid bits left right keys query context model rootMember view installed
    name expressions continuation args (some (.returned value)) run with stopped | reached
  · exact (stopped.2 value rfl).elim
  · exact reached

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.scoped_route_trace
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.scoped_route_returned
