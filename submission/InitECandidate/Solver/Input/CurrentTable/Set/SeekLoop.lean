import InitECandidate.Solver.Input.CurrentTable.Set.SeekStep
import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Loop
import InitECandidate.Solver.Input.CurrentTable.Routing
import InitECandidate.Solver.Input.LoopControlExit

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

theorem SeekState.advance {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base node parent pointer : BitVec 64} {difference : Nat}
    (ready : SeekState origin source base node parent pointer difference) (child : BitVec 64) :
    SeekState origin (bind (bind source "p" node) "n" child) base child node pointer difference := by
  refine ⟨(ready.cursor.with_local "p" node (by decide) (by decide)).with_node child,?_,?_,?_⟩
  · exact (bind_lookup_other (bind source "p" node) "n" "p" child (by decide)).trans (bind_lookup_same _ _ _)
  · exact (bind_lookup_other (bind source "p" node) "n" "d" child (by decide)).trans
      ((bind_lookup_other source "p" "d" node (by decide)).trans ready.differenceCell)
  · exact (bind_lookup_other (bind source "p" node) "n" "key" child (by decide)).trans
      ((bind_lookup_other source "p" "key" node (by decide)).trans ready.keyCell)

def ParentLink (valid : BitVec 64 → Prop) (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64)
    (query : KeyBits.Key) (root node parent : BitVec 64) (difference : Nat) : Prop :=
  (parent = 0#64 ∧ node = root) ∨ valid parent ∧ bits parent < difference ∧
    node = (if KeyBits.bit query (bits parent) then right parent else left parent)

def Seeking (origin source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (base root leaf pointer : BitVec 64) (difference : Nat) (valid : BitVec 64 → Prop)
    (bits : BitVec 64 → Nat) (left right : BitVec 64 → BitVec 64) (query : KeyBits.Key) : Prop :=
  ∃ node parent,SeekState origin source base node parent pointer difference ∧ valid node ∧
    Route bits left right query node leaf ∧ ParentLink valid bits left right query root node parent difference

/-- Only a real continuing insertion step advances the cursor, along the
same route to the earlier actual lookup leaf. -/
theorem seek_progress {origin current target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base root leaf pointer : BitVec 64} {difference : Nat} {valid : BitVec 64 → Prop}
    {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64} {keys : BitVec 64 → KeyBits.Key} {query : KeyBits.Key}
    (image : FindLeaf.Nodes origin base valid bits left right) (model : Routing valid bits left right keys)
    (ready : Seeking origin current base root leaf pointer difference valid bits left right query)
    (marked : bits leaf = 256) (differenceBound : difference ≤ 256) (view : FirstDiff.ByteView origin pointer query)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState (decClockHOLFinite current) seekStep = (result,target))
    (continuing : result = none ∨ result = some .continue) :
    Seeking origin target base root leaf pointer difference valid bits left right query ∧ FindLeaf.rank bits target < FindLeaf.rank bits current := by
  obtain ⟨node,parent,state,member,route,parentLink⟩ := ready
  have stepRun := step_execute image state.at_tick member differenceBound query (view.of_frame state.cursor.at_tick.frame)
  have below : bits node < difference := by
    by_contra notBelow
    have stopped : difference ≤ bits node := by omega
    rw [if_pos stopped] at stepRun
    rw [stepRun] at run
    have resultEq := congrArg Prod.fst run
    dsimp only at resultEq
    rw [←resultEq] at continuing
    simp at continuing
  have active : bits node < 256 := by omega
  rw [if_neg (show ¬difference ≤ bits node from by omega)] at stepRun
  rw [stepRun] at run
  have endpoint := congrArg Prod.snd run
  dsimp only at endpoint
  let child := if KeyBits.bit query (bits node) then right node else left node
  have childMember : valid child := by
    dsimp [child]
    cases digit : KeyBits.bit query (bits node)
    · simpa [digit] using model.leftMember node member active
    · simpa [digit] using model.rightMember node member active
  have greater : bits node < bits child := by
    dsimp [child]
    cases digit : KeyBits.bit query (bits node)
    · simpa [digit] using model.leftGreater node member active
    · simpa [digit] using model.rightGreater node member active
  have nextState : SeekState origin target base child node pointer difference := by
    rw [←endpoint]
    exact state.at_tick.advance child
  have nextRoute : Route bits left right query child leaf := route.head active marked
  have nextParent : ParentLink valid bits left right query root child node difference := Or.inr ⟨member,below,rfl⟩
  refine ⟨⟨child,node,nextState,childMember,nextRoute,nextParent⟩,?_⟩
  have currentWord : FindLeaf.nodeWord current = node := by simp [FindLeaf.nodeWord,state.cursor.nodeCell,valueWord]
  have nextWord : FindLeaf.nodeWord target = child := by simp [FindLeaf.nodeWord,nextState.cursor.nodeCell,valueWord]
  have currentBound := image.bitBound node member
  have nextBound := image.bitBound child childMember
  simp only [FindLeaf.rank,currentWord,nextWord,if_neg (model.nonzero node member),if_neg (model.nonzero child childMember)]
  omega

/-- The unchanged insertion search costs at most257actual source loop
ticks. Its natural rank comes from the reached image and actual next node. -/
theorem seek_cost {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base root leaf pointer : BitVec 64} {difference : Nat} {valid : BitVec 64 → Prop}
    {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64} {keys : BitVec 64 → KeyBits.Key} {query : KeyBits.Key}
    (image : FindLeaf.Nodes origin base valid bits left right) (model : Routing valid bits left right keys)
    (ready : Seeking origin source base root leaf pointer difference valid bits left right query)
    (marked : bits leaf = 256) (differenceBound : difference ≤ 256) (view : FirstDiff.ByteView origin pointer query) :
    source.clock-(evaluateHOLFiniteState source seek).2.clock ≤ 257 := by
  have price := ClockCost.ranked_loop source.code FindLeaf.test seekStep 0
    (fun current => Seeking origin current base root leaf pointer difference valid bits left right query) (FindLeaf.rank bits)
    (ClockCost.of_quiet source.code seekStep (step_quiet source.code))
    (by
      intro current installed state observed actual nonzero
      obtain ⟨node,parent,live,member,route,parentLink⟩ := state
      have word : FindLeaf.nodeWord current = node := by simp [FindLeaf.nodeWord,live.cursor.nodeCell,valueWord]
      have rankPositive : 0 < FindLeaf.rank bits current := by
        have bound := image.bitBound node member
        simp only [FindLeaf.rank,word,if_neg (model.nonzero node member)]
        omega
      refine ⟨rankPositive,?_⟩
      intro funded
      dsimp only
      intro continuing
      exact seek_progress image model ⟨node,parent,live,member,route,parentLink⟩ marked differenceBound view _ rfl continuing)
    source rfl ready
  rw [←seek_shapes.2.1] at price
  simp only [Nat.zero_add,Nat.one_mul] at price
  exact Nat.le_trans price (by unfold FindLeaf.rank; split <;> omega)

/-- A real normal search exits at its actual b≥d guard, retaining the
parent edge and route needed by the original subsequent insertion writes. -/
theorem seek_finished {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base root leaf pointer : BitVec 64} {difference : Nat} {valid : BitVec 64 → Prop}
    {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64} {keys : BitVec 64 → KeyBits.Key} {query : KeyBits.Key}
    (image : FindLeaf.Nodes origin base valid bits left right) (model : Routing valid bits left right keys)
    (ready : Seeking origin source base root leaf pointer difference valid bits left right query)
    (marked : bits leaf = 256) (differenceBound : difference ≤ 256) (view : FirstDiff.ByteView origin pointer query)
    (normal : evaluateHOLFiniteState source seek = (none,post)) :
    ∃ node parent,SeekState origin post base node parent pointer difference ∧ valid node ∧ difference ≤ bits node ∧
      Route bits left right query node leaf ∧ ParentLink valid bits left right query root node parent difference := by
  rw [seek_shapes.2.1] at normal
  apply loop_control_exit FindLeaf.test seekStep
    (fun current => Seeking origin current base root leaf pointer difference valid bits left right query)
    (fun current => ∃ node parent,SeekState origin current base node parent pointer difference ∧ valid node ∧ difference ≤ bits node ∧
      Route bits left right query node leaf ∧ ParentLink valid bits left right query root node parent difference) _ _ _ source post ready normal
  · intro current state stopped
    obtain ⟨node,parent,live,member,route,parentLink⟩ := state
    have read := FindLeaf.test_read current node live.cursor.nodeCell
    rw [if_neg (model.nonzero node member)] at read
    have impossible := stopped.symm.trans read
    cases impossible
  · intro current state observed actual nonzero funded target result run continuing
    exact (seek_progress image model state marked differenceBound view result run continuing).1
  · intro current state observed actual nonzero funded target run
    obtain ⟨node,parent,live,member,route,parentLink⟩ := state
    have stepRun := step_execute image live.at_tick member differenceBound query (view.of_frame live.cursor.at_tick.frame)
    by_cases stopped : difference ≤ bits node
    · rw [if_pos stopped] at stepRun
      rw [stepRun] at run
      have endpoint := congrArg Prod.snd run
      dsimp only at endpoint
      rw [←endpoint]
      exact ⟨node,parent,live.at_tick,member,stopped,route,parentLink⟩
    · rw [if_neg stopped] at stepRun
      rw [stepRun] at run
      cases run

/-- The actual earlier first-difference result makes the insertion split
strict on both sides of its remembered parent edge. -/
theorem seek_finished_strict {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base root leaf pointer : BitVec 64} {difference : Nat} {valid : BitVec 64 → Prop}
    {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64} {keys : BitVec 64 → KeyBits.Key} {query : KeyBits.Key}
    (image : FindLeaf.Nodes origin base valid bits left right) (model : Routing valid bits left right keys)
    (ready : Seeking origin source base root leaf pointer difference valid bits left right query)
    (marked : bits leaf = 256) (differenceInside : difference < 256) (view : FirstDiff.ByteView origin pointer query)
    (first : KeyBits.First query (keys leaf) difference)
    (normal : evaluateHOLFiniteState source seek = (none,post)) :
    ∃ node parent,SeekState origin post base node parent pointer difference ∧ valid node ∧ difference < bits node ∧
      Route bits left right query node leaf ∧ ParentLink valid bits left right query root node parent difference := by
  obtain ⟨node,parent,state,member,stopped,route,parentLink⟩ := seek_finished image model ready marked (by omega) view normal
  exact ⟨node,parent,state,member,route.stop_strict model member marked first differenceInside stopped,route,parentLink⟩

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.seek_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.seek_finished
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.seek_finished_strict

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual n is the finite control. p remains in range but does not
influence the unchanged search's next guard or branch. -/
def RangeSeeking (origin source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (base pointer : BitVec 64) (difference limit : Nat) : Prop:=
  ∃ node parent,SeekState origin source base node parent pointer difference ∧ node.toNat<limit ∧ parent.toNat<limit

noncomputable def rangeNext (origin : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (difference limit : Nat) (positive : 0<limit)
    (bits left right : BitVec 64 → BitVec 64) (index : Fin limit) : Option (Fin limit):=
  let node:=BitVec.ofNat 64 index.val
  if node=0#64 then none else
  if difference≤(bits node).toNat then none else
  match FindLeaf.keyProbe origin pointer (bits node) with
  | some (.val (.word choice)) =>
      some (FindLeaf.rangeIndex limit positive (if choice=0#64 then right node else left node))
  | _ => none

theorem range_next_at {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base node parent pointer : BitVec 64} {difference limit : Nat} (positive : 0<limit)
    (bits left right : BitVec 64 → BitVec 64) (ready : SeekState origin source base node parent pointer difference)
    (inside : node.toNat<limit) :
    rangeNext origin pointer difference limit positive bits left right (FindLeaf.rangeIndex limit positive (FindLeaf.nodeWord source))=
      if node=0#64 then none else if difference≤(bits node).toNat then none else
      match FindLeaf.keyProbe origin pointer (bits node) with
      | some (.val (.word choice)) =>
          some (FindLeaf.rangeIndex limit positive (if choice=0#64 then right node else left node))
      | _ => none := by
  have current : FindLeaf.nodeWord source=node:=by simp [FindLeaf.nodeWord,ready.cursor.nodeCell,valueWord]
  simp only [rangeNext,current,FindLeaf.rangeIndex,Nat.mod_eq_of_lt inside,BitVec.ofNat_toNat,BitVec.setWidth_eq]

/-- Relate the original step, including its real errors, to the fixed
finite transition. No routing or strict bit order is assumed. -/
theorem range_step_model {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base node parent pointer marker : BitVec 64} {difference limit : Nat} (positive : 0<limit)
    {bits left right : BitVec 64 → BitVec 64}
    (image : FindLeaf.RangeNodes origin base marker limit bits left right)
    (ready : SeekState origin source base node parent pointer difference)
    (nonzero : node≠0#64) (inside : node.toNat<limit) (bounded : difference≤marker.toNat) :
    let output:=evaluateHOLFiniteState source seekStep
    ((output.1=none ∨ output.1=some .continue) →
      RangeSeeking origin output.2 base pointer difference limit ∧
      rangeNext origin pointer difference limit positive bits left right (FindLeaf.rangeIndex limit positive (FindLeaf.nodeWord source))=
        some (FindLeaf.rangeIndex limit positive (FindLeaf.nodeWord output.2))) ∧
    (¬(output.1=none ∨ output.1=some .continue) →
      rangeNext origin pointer difference limit positive bits left right (FindLeaf.rangeIndex limit positive (FindLeaf.nodeWord source))=none) := by
  dsimp only
  rw [range_step_execute image ready nonzero inside bounded,range_next_at positive bits left right ready inside]
  simp only [if_neg nonzero]
  by_cases stopped : difference≤(bits node).toNat
  · simp only [if_pos stopped]
    simp
  · simp only [if_neg stopped]
    have internal : bits node≠marker:=by intro same; rw [same] at stopped; omega
    generalize observed : FindLeaf.keyProbe origin pointer (bits node)=value
    cases value with
    | none=>simp
    | some value=>
      cases value with
      | rStruct fields=>simp
      | nStruct name fields=>simp
      | val payload=>
        cases payload with
        | word choice=>
          let child:=if choice=0#64 then right node else left node
          have childInside : child.toNat<limit:=by
            dsimp only [child]
            split
            · exact image.rightRange node nonzero inside internal
            · exact image.leftRange node nonzero inside internal
          have childState:=ready.advance child
          constructor
          · intro continuing
            refine ⟨⟨child,node,childState,childInside,inside⟩,?_⟩
            simp only [FindLeaf.nodeWord,bind_lookup_same,Option.getD_some,valueWord]
          · simp

/-- A non-timeout execution of the actual insertion search spends at
most one source tick per possible n. Termination is taken from that same
observed run, with failed tests and break exits retained. -/
theorem range_seek_cost {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base node parent pointer marker : BitVec 64} {difference limit : Nat}
    {bits left right : BitVec 64 → BitVec 64}
    (image : FindLeaf.RangeNodes origin base marker limit bits left right)
    (ready : SeekState origin source base node parent pointer difference)
    (inside : node.toNat<limit) (parentInside : parent.toNat<limit) (bounded : difference≤marker.toNat)
    (notTimeout : (evaluateHOLFiniteState source seek).1≠some .timeOut) :
    source.clock-(evaluateHOLFiniteState source seek).2.clock≤limit := by
  have positive : 0<limit:=by omega
  rw [seek_shapes.2.1] at notTimeout ⊢
  have paid:=ClockCost.finite_control_loop_terminating source.code FindLeaf.test seekStep 0
    (ClockCost.of_quiet source.code seekStep (step_quiet source.code))
    (fun current=>RangeSeeking origin current base pointer difference limit)
    (fun current=>FindLeaf.rangeIndex limit positive (FindLeaf.nodeWord current))
    (rangeNext origin pointer difference limit positive bits left right)
    (by
      intro current installed state inactive
      obtain ⟨currentNode,currentParent,state,currentInside,parentInside⟩:=state
      have zero : currentNode=0#64:=by
        by_contra nonzero
        have expected:=FindLeaf.test_read current currentNode state.cursor.nodeCell
        rw [if_neg nonzero] at expected
        exact inactive ⟨1#64,expected,by decide⟩
      rw [range_next_at positive bits left right state currentInside,if_pos zero])
    (by
      intro current installed state observed read nonzero funded
      obtain ⟨currentNode,currentParent,state,currentInside,parentInside⟩:=state
      have nodeNe : currentNode≠0#64:=by
        intro zero
        have expected:=FindLeaf.test_read current currentNode state.cursor.nodeCell
        rw [if_pos zero] at expected
        have equal : observed=0#64:=by
          simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
        exact nonzero equal
      exact range_step_model positive image state.at_tick nodeNe currentInside bounded)
    source rfl ⟨node,parent,ready,inside,parentInside⟩ notTimeout
  simpa only [Nat.zero_add,Nat.one_mul,Fintype.card_fin] using paid

/-- The normal original search reaches its actual zero/unsigned-stop
condition with both n and p in range, and the complete physical frame. -/
theorem range_seek_finished {origin source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base node parent pointer marker : BitVec 64} {difference limit : Nat}
    {bits left right : BitVec 64 → BitVec 64}
    (image : FindLeaf.RangeNodes origin base marker limit bits left right)
    (ready : SeekState origin source base node parent pointer difference)
    (inside : node.toNat<limit) (parentInside : parent.toNat<limit) (bounded : difference≤marker.toNat)
    (normal : evaluateHOLFiniteState source seek=(none,post)) :
    ∃ node parent,SeekState origin post base node parent pointer difference ∧
      node.toNat<limit ∧ parent.toNat<limit ∧ (node=0#64 ∨ difference≤(bits node).toNat) := by
  have positive : 0<limit:=by omega
  rw [seek_shapes.2.1] at normal
  apply loop_control_exit FindLeaf.test seekStep
    (fun current=>RangeSeeking origin current base pointer difference limit)
    (fun current=>∃ node parent,SeekState origin current base node parent pointer difference ∧
      node.toNat<limit ∧ parent.toNat<limit ∧ (node=0#64 ∨ difference≤(bits node).toNat)) _ _ _ source post ⟨node,parent,ready,inside,parentInside⟩ normal
  · intro current state inactive
    obtain ⟨node,parent,state,inside,parentInside⟩:=state
    have zero : node=0#64:=by
      by_contra nonzero
      have expected:=FindLeaf.test_read current node state.cursor.nodeCell
      rw [if_neg nonzero] at expected
      have impossible:=inactive.symm.trans expected
      cases impossible
    exact ⟨node,parent,state,inside,parentInside,Or.inl zero⟩
  · intro current state word read nonzero funded target result executed continuing
    obtain ⟨node,parent,state,inside,parentInside⟩:=state
    have nodeNe : node≠0#64:=by
      intro zero
      have expected:=FindLeaf.test_read current node state.cursor.nodeCell
      rw [if_pos zero] at expected
      have equal : word=0#64:=by
        simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
      exact nonzero equal
    have model:=(range_step_model positive image state.at_tick nodeNe inside bounded).1
    rw [executed] at model
    exact (model continuing).1
  · intro current state word read nonzero funded target executed
    obtain ⟨node,parent,state,inside,parentInside⟩:=state
    have nodeNe : node≠0#64:=by
      intro zero
      have expected:=FindLeaf.test_read current node state.cursor.nodeCell
      rw [if_pos zero] at expected
      have equal : word=0#64:=by
        simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
      exact nonzero equal
    have stepRun:=range_step_execute image state.at_tick nodeNe inside bounded
    by_cases stopped : difference≤(bits node).toNat
    · rw [if_pos stopped] at stepRun
      rw [stepRun] at executed
      have endpoint:=congrArg Prod.snd executed
      dsimp only at endpoint
      rw [←endpoint]
      exact ⟨node,parent,state.at_tick,inside,parentInside,Or.inr stopped⟩
    · rw [if_neg stopped] at stepRun
      rw [stepRun] at executed
      generalize observed : FindLeaf.keyProbe origin pointer (bits node)=value at executed
      cases value with
      | none=>cases executed
      | some value=>
        cases value with
        | rStruct fields=>cases executed
        | nStruct name fields=>cases executed
        | val payload=>cases payload with | word choice=>cases executed

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.range_next_at
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.range_step_model
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.range_seek_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.range_seek_finished
