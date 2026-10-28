import InitECandidate.Solver.Input.CurrentTable.FindLeaf.Step
import InitECandidate.Solver.Input.ClockCostLoop

namespace InitECandidate.Solver.Input.CurrentTable.FindLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def nodeWord (source : PanSemStateFiniteExact 64 Guest.HostMemory) : BitVec 64 :=
  valueWord ((source.locals.lookup (ofString "n")).getD (.val (.word 0#64)))
def rank (bits : BitVec 64 → Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat :=
  if nodeWord source=0#64 then 0 else 257-bits (nodeWord source)
def Invariant (origin : PanSemStateFiniteExact 64 Guest.HostMemory) (base : BitVec 64) (valid : BitVec 64 → Prop)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ node,State origin source base node ∧ (node=0#64 ∨ valid node)

theorem test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "n")=some (.val (.word node))) :
    evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=
      some (.val (.word (if node=0#64 then 0#64 else 1#64))) := by
  by_cases zero : node=0#64
  · simp [test,evalHOLFinite,evalHOLExact,toExact,localVar,nodeCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]
  · simp [test,evalHOLFinite,evalHOLExact,toExact,localVar,nodeCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,zero]

set_option maxHeartbeats 2000000 in
theorem transition {origin : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : Nodes origin base valid bits left right) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ready : Invariant origin base valid source) (observed : BitVec 64)
    (read : evalHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) test=some (.val (.word observed)))
    (nonzero : observed≠0#64) : 0<rank bits source ∧
      (source.clock≠0 → let output:=evaluateHOLFiniteState (decClockHOLFinite source) step;
        (output.1=none ∨ output.1=some .continue) → Invariant origin base valid output.2 ∧ rank bits output.2<rank bits source) := by
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
  have currentRank : rank bits source=257-bits node := by simp [rank,currentWord,nodeNe]
  have bitBound:=image.bitBound node member
  refine ⟨by rw [currentRank]; omega,?_⟩
  intro funded
  dsimp only
  intro continuing
  generalize computed : evaluateHOLFiniteState (decClockHOLFinite source) step=output at continuing ⊢
  obtain ⟨result,target⟩:=output
  obtain ⟨child,normal,postEq,ordered⟩:=step_progress image state.at_tick member result computed continuing
  have nextState : State origin target base child := by rw [postEq]; exact state.at_tick.with_node child
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

/-- The actual current read-only Patricia traversal loop spends at most
257source ticks when its reached node image has strictly increasing bit
positions. Establishing that image from the real insertion history remains
required before this helper is a whole-program bound. -/
theorem loop_cost {origin source : PanSemStateFiniteExact 64 Guest.HostMemory} {base : BitVec 64}
    {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    (image : Nodes origin base valid bits left right) (ready : Invariant origin base valid source) :
    source.clock-(evaluateHOLFiniteState source loop).2.clock≤257 := by
  have price:=ClockCost.ranked_loop source.code test step 0 (Invariant origin base valid) (rank bits)
    (ClockCost.of_quiet source.code step (step_quiet source.code))
    (by intro current codeEq state observed read nonzero; exact transition image current state observed read nonzero) source rfl ready
  rw [←shapes.1] at price
  simp only [Nat.zero_add,Nat.one_mul] at price
  exact Nat.le_trans price (by unfold rank; split <;> omega)

end InitECandidate.Solver.Input.CurrentTable.FindLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.test_read
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.transition
#print axioms InitECandidate.Solver.Input.CurrentTable.FindLeaf.loop_cost
