import InitECandidate.Solver.Mpt.DeleteUnwindChoiceCost
import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Uniform intermediate source allowance from the physical path extent.
This is not a whole-program target bound; copy/heap amortization can tighten
its later composition across many mutations. -/
def unwindAllowance (pathLower : Nat) : Nat:=2*((33806089496-pathLower)/8)+40

theorem unwind_iteration_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : UnwindModel source limit nodeLower pathLower property) (active : model.top≠0#64) :
    source.clock-(evaluateHOLFiniteState source unwindBody).2.clock≤2*((model.heap.toNat-pathLower)/8)+40 := by
  obtain ⟨saved,tail,framesEq,topEq,view,_previous,_rest,_decreases⟩:=model.stack.pop source model.cursor.toNat model.top model.frames active
  have owned : saved.Owned model.graph:=model.parents saved (by rw [framesEq]; simp)
  have topCell : source.locals.lookup (ofString "top")=some (.val (.word saved.pointer)):=by rw [←topEq]; exact model.topCell
  have read:=view.node_read source saved model.scratch.domain topCell
  let enteredState:=QueryBranch.bind source "fnode" saved.node
  let entered:=model.bind_other source limit nodeLower pathLower property "fnode" saved.node (by decide) (by decide)
  have enteredView : saved.View enteredState:=view.of_memory source enteredState saved (by intros; rfl)
  have enteredNode : enteredState.locals.lookup (ofString "fnode")=some (.val (.word saved.node)):=bind_lookup_same _ _ _
  have chosen:=unwind_choice_cost enteredState limit nodeLower pathLower property entered saved enteredView owned topEq enteredNode
  have popped : Input.ClockCost.Bound enteredState.code pop 0:=by
    rw [unwind_shapes.2.2.2.2]
    exact Input.ClockCost.assign enteredState.code (ofString "top") (field "top" 0#64)
  have priced:=Input.ClockCost.sequence_current enteredState unwindChoice pop (2*((model.heap.toNat-pathLower)/8)+40) 0 chosen popped
  rw [unwind_shapes.2.1]
  apply Input.ClockCost.declared_current source "fnode" (field "top" 8#64) saved.node afterFrameNode _ read
  rw [unwind_shapes.2.2.1]
  exact priced

/-- Same all-outcome bound uniformly across the actual bounded heap. -/
theorem unwind_iteration_uniform_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : UnwindModel source limit nodeLower pathLower property) (active : model.top≠0#64) :
    source.clock-(evaluateHOLFiniteState source unwindBody).2.clock≤unwindAllowance pathLower := by
  have priced:=unwind_iteration_cost source limit nodeLower pathLower property model active
  have heapBound : model.heap.toNat≤33806089496:=model.heapArena.upper
  have difference:=Nat.sub_le_sub_right heapBound pathLower
  have quotient : (model.heap.toNat-pathLower)/8≤(33806089496-pathLower)/8:=Nat.div_le_div_right difference
  unfold unwindAllowance
  omega

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.unwind_iteration_cost
#print axioms InitECandidate.Solver.Mpt.DeleteBody.unwind_iteration_uniform_cost
