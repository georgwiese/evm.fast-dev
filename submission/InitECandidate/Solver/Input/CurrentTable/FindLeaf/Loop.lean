import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Step
import InitECandidate.Solver.Input.ClockCostLoop
import InitECandidate.Solver.Input.ClockCostTerminatingLoop

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def nodeWord (source : PanSemStateFiniteExact 64 Guest.HostMemory) : BitVec 64 :=
  valueWord ((source.locals.lookup (ofString "n")).getD (.val (.word 0#64)))
def rank (bits : BitVec 64 → Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (marker : Nat:=256) : Nat :=
  if nodeWord source=0#64 then 0 else (marker+1)-bits (nodeWord source)
def Invariant (origin : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (valid : BitVec 64 → Prop)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (marker : BitVec 64:=256#64) : Prop :=
  ∃ node,State origin source base node marker ∧ (node=0#64 ∨ valid node)

theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "n")=some (.val (.word node))) :
    evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=
      some (.val (.word (if node=0#64 then 0#64 else 1#64))) := by
  by_cases zero : node=0#64
  · simp [test,evalHOLFinite,evalHOLExact,toExact,localVar,nodeCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]
  · simp [test,evalHOLFinite,evalHOLExact,toExact,localVar,nodeCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]

theorem State.active {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base node marker observed : BitVec 64} (ready : State origin source base node marker)
    (read : evalHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) test = some (.val (.word observed)))
    (nonzero : observed ≠ 0#64) : node ≠ 0#64 := by
  intro zero
  have expected := test_read source node ready.nodeCell
  rw [if_pos zero] at expected
  have equal : observed = 0#64 := by
    simpa only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero equal

set_option maxHeartbeats 2000000 in
theorem transition {origin : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {marker : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : Nodes origin base valid bits left right marker.toNat) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ready : Invariant origin base valid source marker) (observed : BitVec 64)
    (read : evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=some (.val (.word observed)))
    (nonzero : observed≠0#64) : 0<rank bits source marker.toNat ∧
      (source.clock≠0 → let output:=evaluateHOLFiniteState (decClockHOLFinite source) step;
        (output.1=none ∨ output.1=some .continue) → Invariant origin base valid output.2 marker ∧ rank bits output.2 marker.toNat<rank bits source marker.toNat) := by
  obtain ⟨node,state,present⟩:=ready
  have expected:=test_read source node state.nodeCell
  have nodeNe : node≠0#64 := by
    intro zero
    rw [if_pos zero] at expected
    have equal : observed=0#64 := by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
    exact nonzero equal
  have member:=present.resolve_left nodeNe
  have currentWord : nodeWord source=node := by simp [nodeWord,state.nodeCell,valueWord]
  have currentRank : rank bits source marker.toNat=(marker.toNat+1)-bits node := by simp [rank,currentWord,nodeNe]
  have bitBound:=image.bitBound node member
  refine ⟨by rw [currentRank]; omega,?_⟩
  intro funded
  dsimp only
  intro continuing
  generalize computed : evaluateHOLFiniteState (decClockHOLFinite source) step=output at continuing ⊢
  obtain ⟨result,target⟩:=output
  obtain ⟨child,normal,postEq,ordered⟩:=step_progress image state.at_tick member result computed continuing
  have nextState : State origin target base child marker := by rw [postEq]; exact state.at_tick.with_node child
  have nextPresent : child=0#64 ∨ valid child := ordered.imp_right And.left
  have nextWord : nodeWord target=child := by simp [nodeWord,nextState.nodeCell,valueWord]
  refine ⟨⟨child,nextState,nextPresent⟩,?_⟩
  rw [currentRank]
  by_cases zero : child=0#64
  · simp only [rank,nextWord,if_pos zero]
    omega
  · have next:=ordered.resolve_left zero
    have nextBound:=image.bitBound child next.1
    simp only [rank,nextWord,if_neg zero]
    omega

/-- The actual read-only traversal spends at most marker+1 source ticks
when its reached node image has strictly increasing bit positions. The
image must still come from actual insertion history before this helper
contributes to a whole-program bound. -/
theorem loop_marker_cost {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64} {marker : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : Nodes origin base valid bits left right marker.toNat) (ready : Invariant origin base valid source marker) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤marker.toNat+1 := by
  have price:=ClockCost.ranked_loop source.code test step 0 (fun state=>Invariant origin base valid state marker) (fun state=>rank bits state marker.toNat)
    (ClockCost.of_quiet source.code step (step_quiet source.code))
    (by intro current codeEq state observed read nonzero; exact transition image current state observed read nonzero) source rfl ready
  rw [←shapes.1] at price
  simp only [Nat.zero_add,Nat.one_mul] at price
  exact Nat.le_trans price (by unfold rank; split <;> omega)

theorem loop_cost {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : Nodes origin base valid bits left right) (ready : Invariant origin base valid source) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤257 :=
  loop_marker_cost image ready

def rangeIndex (limit : Nat) (positive : 0 < limit) (node : BitVec 64) : Fin limit :=
  ⟨node.toNat % limit, Nat.mod_lt _ positive⟩

noncomputable def rangeNext (origin : PanSemStateFiniteExact 64 Guest.HostMemory)
    (key marker : BitVec 64) (limit : Nat) (positive : 0 < limit)
    (bits left right : BitVec 64 → BitVec 64) (index : Fin limit) : Option (Fin limit) :=
  let node := BitVec.ofNat 64 index.val
  if node = 0#64 then none else
  if bits node = marker then none else
  match keyProbe origin key (bits node) with
  | some (.val (.word choice)) =>
      some (rangeIndex limit positive (if choice = 0#64 then right node else left node))
  | _ => none

def RangeInvariant (origin : PanSemStateFiniteExact 64 Guest.HostMemory)
    (base key marker : BitVec 64) (limit : Nat)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ node, State origin source base node marker ∧
    source.locals.lookup (ofString "key") = some (.val (.word key)) ∧ node.toNat < limit

theorem range_next_at {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base key marker node : BitVec 64} {limit : Nat} (positive : 0 < limit)
    (bits left right : BitVec 64 → BitVec 64) (ready : State origin source base node marker)
    (inside : node.toNat < limit) :
    rangeNext origin key marker limit positive bits left right (rangeIndex limit positive (nodeWord source)) =
      if node = 0#64 then none else if bits node = marker then none else
      match keyProbe origin key (bits node) with
      | some (.val (.word choice)) =>
          some (rangeIndex limit positive (if choice = 0#64 then right node else left node))
      | _ => none := by
  have current : nodeWord source = node := by simp [nodeWord, ready.nodeCell, valueWord]
  simp only [rangeNext, current, rangeIndex, Nat.mod_eq_of_lt inside, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The deterministic finite control model is derived from the original
single-step evaluator, including actual aborts and lexical restoration. -/
theorem range_step_model {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base node marker key : BitVec 64} {limit : Nat} (positive : 0 < limit)
    {bits left right : BitVec 64 → BitVec 64}
    (image : RangeNodes origin base marker limit bits left right)
    (ready : State origin source base node marker)
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word key)))
    (nonzero : node ≠ 0#64) (inside : node.toNat < limit) :
    let output := evaluateHOLFiniteState source step
    ((output.1 = none ∨ output.1 = some .continue) →
      RangeInvariant origin base key marker limit output.2 ∧
      rangeNext origin key marker limit positive bits left right (rangeIndex limit positive (nodeWord source)) =
        some (rangeIndex limit positive (nodeWord output.2))) ∧
    (¬ (output.1 = none ∨ output.1 = some .continue) →
      rangeNext origin key marker limit positive bits left right (rangeIndex limit positive (nodeWord source)) = none) := by
  dsimp only
  rw [range_step_execute image ready keyCell nonzero inside, range_next_at positive bits left right ready inside]
  simp only [if_neg nonzero]
  by_cases leaf : bits node = marker
  · simp only [if_pos leaf]
    simp
  · simp only [if_neg leaf]
    generalize observed : keyProbe origin key (bits node) = value
    cases value with
    | none => simp
    | some value =>
      cases value with
      | rStruct fields => simp
      | nStruct name fields => simp
      | val payload =>
        cases payload with
        | word choice =>
          let child := if choice = 0#64 then right node else left node
          have childInside : child.toNat < limit := by
            dsimp only [child]
            split
            · exact image.rightRange node nonzero inside leaf
            · exact image.leftRange node nonzero inside leaf
          have childState := ready.with_node child
          have childKey : (bind source "n" child).locals.lookup (ofString "key") = some (.val (.word key)) :=
            (bind_lookup_other source "n" "key" child (by decide)).trans keyCell
          constructor
          · intro continuing
            refine ⟨⟨child, childState, childKey, childInside⟩, ?_⟩
            simp only [nodeWord, bind_lookup_same, Option.getD_some, valueWord]
          · simp

/-- A genuinely non-timeout traversal costs at most the actual node-index
range. No increasing-bit, routing, key-read success or future leaf premise
is needed. The range image must come from the actual table history. -/
theorem range_loop_cost {origin source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {base node marker key : BitVec 64} {limit : Nat} {bits left right : BitVec 64 → BitVec 64}
    (image : RangeNodes origin base marker limit bits left right)
    (ready : State origin source base node marker)
    (keyCell : source.locals.lookup (ofString "key") = some (.val (.word key)))
    (inside : node.toNat < limit)
    (notTimeout : (evaluateHOLFiniteState source loop).1 ≠ some .timeOut) :
    source.clock - (evaluateHOLFiniteState source loop).2.clock ≤ limit := by
  have positive : 0 < limit := by omega
  rw [shapes.1] at notTimeout ⊢
  have paid := ClockCost.finite_control_loop_terminating source.code test step 0
    (ClockCost.of_quiet source.code step (step_quiet source.code))
    (RangeInvariant origin base key marker limit)
    (fun current => rangeIndex limit positive (nodeWord current))
    (rangeNext origin key marker limit positive bits left right)
    (by
      intro current installed state inactive
      obtain ⟨currentNode, state, currentKey, currentInside⟩ := state
      have zero : currentNode = 0#64 := by
        by_contra nonzero
        have expected := test_read current currentNode state.nodeCell
        rw [if_neg nonzero] at expected
        exact inactive ⟨1#64, expected, by decide⟩
      rw [range_next_at positive bits left right state currentInside, if_pos zero])
    (by
      intro current installed state observed read nonzero funded
      obtain ⟨currentNode, state, currentKey, currentInside⟩ := state
      have nodeNe := state.active read nonzero
      exact range_step_model positive image state.at_tick currentKey nodeNe currentInside)
    source rfl ⟨node, ready, keyCell, inside⟩ notTimeout
  simpa only [Nat.zero_add, Nat.one_mul, Fintype.card_fin] using paid

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.test_read
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.transition
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.loop_cost

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.loop_marker_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.range_next_at
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.range_step_model
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.range_loop_cost
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.State.active
