import InitECandidate.Solver.Input.CurrentTable.FindLeaf.KeyBranch
import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Context
import InitECandidate.Solver.Input.CurrentTable.Routing

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem step_leaf_execute {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base node : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : Nodes origin base valid bits left right) (ready : State origin source base node)
    (member : valid node) (marked : bits node = 256) :
    evaluateHOLFiniteState source step = (some .break,source) := by
  let entered := bind source "b" (BitVec.ofNat 64 (bits node))
  have state := ready.with_bit (BitVec.ofNat 64 (bits node))
  have afterRun := after_bit_execute entered (bits node) (image.bitBound node member) (bind_lookup_same _ _ _) state.bitsCell
  rw [if_pos marked] at afterRun
  have actual := ScalarScope.declare_execute source entered "b" (.load .one (address 24))
    (BitVec.ofNat 64 (bits node)) afterBit (some .break) (bit_read image ready member) afterRun
  rw [shapes.2.1,actual,restore_bound]

def Routed (origin source : PanSemStateFiniteExact 64 Guest.HostMemory) (base root pointer : BitVec 64)
    (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64) (query : KeyBits.Key) : Prop :=
  ∃ node,State origin source base node ∧ valid node ∧ Route bits left right query root node ∧
    source.locals.lookup (ofString "key") = some (.val (.word pointer))

/-- A normal current lookup of a nonempty properly routed image supplies
its genuine finite query route to the returned leaf. -/
theorem loop_route {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory} {base root pointer : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {query : KeyBits.Key}
    (image : Nodes origin base valid bits left right) (model : Routing valid bits left right keys)
    (ready : Routed origin source base root pointer valid bits left right query)
    (view : FirstDiff.ByteView origin pointer query)
    (normal : evaluateHOLFiniteState source loop = (none,post)) :
    ∃ leaf,State origin post base leaf ∧ valid leaf ∧ bits leaf = 256 ∧ Route bits left right query root leaf := by
  rw [shapes.1] at normal
  apply loop_control_exit test step (fun current => Routed origin current base root pointer valid bits left right query)
    (fun current => ∃ leaf,State origin current base leaf ∧ valid leaf ∧ bits leaf = 256 ∧ Route bits left right query root leaf)
    _ _ _ source post ready normal
  · intro current validState stopped
    obtain ⟨node,state,member,route,keyCell⟩ := validState
    have read := test_read current node state.nodeCell
    rw [if_neg (model.nonzero node member)] at read
    have impossible := stopped.symm.trans read
    cases impossible
  · intro current validState observed actual nonzero funded target result run continuing
    obtain ⟨node,state,member,route,keyCell⟩ := validState
    have internal : bits node < 256 := by
      by_contra outside
      have marked : bits node = 256 := by have := image.bitBound node member; omega
      have leafRun := step_leaf_execute image state.at_tick member marked
      rw [leafRun] at run
      have equal := congrArg Prod.fst run
      dsimp only at equal
      rw [←equal] at continuing
      simp at continuing
    let child := if KeyBits.bit query (bits node) then right node else left node
    have stepRun := step_execute image state.at_tick member internal pointer query keyCell (view.of_frame state.at_tick.frame)
    rw [stepRun] at run
    have endpoint := congrArg Prod.snd run
    dsimp only at endpoint
    have nextMember : valid child := by
      dsimp [child]
      cases digit : KeyBits.bit query (bits node)
      · simpa [digit] using model.leftMember node member internal
      · simpa [digit] using model.rightMember node member internal
    have nextRoute : Route bits left right query root child := route.trans (by
      dsimp [child]
      cases digit : KeyBits.bit query (bits node)
      · simpa [digit] using Route.left (bits:=bits) (left:=left) (right:=right) (query:=query) node (left node) internal digit (.here _)
      · simpa [digit] using Route.right (bits:=bits) (left:=left) (right:=right) (query:=query) node (right node) internal digit (.here _))
    rw [←endpoint]
    exact ⟨child,state.at_tick.with_node child,nextMember,nextRoute,
      (bind_lookup_other (decClockHOLFinite current) "n" "key" child (by decide)).trans keyCell⟩
  · intro current validState observed actual nonzero funded target run
    obtain ⟨node,state,member,route,keyCell⟩ := validState
    obtain ⟨marked,endpoint⟩ := step_break image state.at_tick member run
    rw [endpoint]
    exact ⟨node,state.at_tick,member,marked,route⟩

/-- The real body return retains the actual route just derived from its
same normal loop, with no independently supplied successful lookup. -/
theorem Context.returned_route {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {table base root pointer : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {query : KeyBits.Key}
    (ready : Context source table base root valid bits left right) (model : Routing valid bits left right keys)
    (rootMember : valid root)
    (tableCell : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word pointer)))
    (view : FirstDiff.ByteView source pointer query)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value),post)) :
    ∃ leaf,value = .val (.word leaf) ∧ valid leaf ∧ bits leaf = 256 ∧ Route bits left right query root leaf ∧
      LocalEffects.erase post = LocalEffects.erase source := by
  have original := normal
  rw [setup_execute source table base root ready.domain ready.arena ready.aligned tableCell ready.keyCell ready.nodesCell ready.rootCell] at normal
  let afterPost := (evaluateHOLFiniteState (rootEntry source base root) afterRoot).2
  have observed := congrArg Prod.fst normal
  dsimp only at observed
  have afterRun : evaluateHOLFiniteState (rootEntry source base root) afterRoot = (some (.returned value),afterPost) := Prod.ext observed rfl
  have initial : Invariant source base valid (rootEntry source base root) := ⟨root,root_state source base root,Or.inr rootMember⟩
  rw [body_shapes.2.2.2] at afterRun
  obtain ⟨loopPost,loopRun,returnedRun⟩ := sequence_returned (rootEntry source base root) afterPost loop (.return (localVar "n")) value
    (loop_never ready.image initial) afterRun
  have firstKey := (bind_lookup_other source "keybits" "key" 256#64 (by decide)).trans keyCell
  have secondKey := (bind_lookup_other (bitsEntry source) "nodes" "key" base (by decide)).trans firstKey
  have finalKey := (bind_lookup_other (nodesEntry source base) "n" "key" root (by decide)).trans secondKey
  have routed : Routed source (rootEntry source base root) base root pointer valid bits left right query :=
    ⟨root,root_state source base root,rootMember,.here root,finalKey⟩
  obtain ⟨leaf,state,member,marked,route⟩ := loop_route ready.image model routed view loopRun
  have expected : evaluateHOLFiniteState loopPost (.return (localVar "n")) =
      (some (.returned (.val (.word leaf))),emptyLocalsHOLFinite loopPost) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,localVar,state.nodeCell,shapeOfHOLExact]
  rw [expected] at returnedRun
  have answer : value = .val (.word leaf) := by
    simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using (congrArg Prod.fst returnedRun).symm
  have frame := body_readonly source.code source rfl
  rw [original] at frame
  exact ⟨leaf,answer,member,marked,route,frame⟩

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.loop_route
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.Context.returned_route
