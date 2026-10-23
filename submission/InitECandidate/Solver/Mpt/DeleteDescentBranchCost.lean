import InitECandidate.Solver.Mpt.DeleteDescentBranchValueMemory
import InitECandidate.Solver.Mpt.CollapseBranchCost
import InitECandidate.Solver.Input.ClockCostAssignedCurrent
import InitECandidate.Solver.Arenas.Cost
import InitECandidate.Solver.Mpt.DeleteFrameProgram

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual nibble declaration and entire scratch push cost at most
two source ticks on every outcome, including failed allocation. -/
theorem branch_scope_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code branchIndexScope 2 := by
  rw [branch_index_shape]
  apply Input.ClockCost.declared code (ofString "idx") .one branchIndex branchFrameScope 2
  rw [branch_shapes.2.2.1]
  exact Arenas.scoped_price code installed .down (ofString "fr2") .one [.const 40#64] branchPush 0
    (Input.ClockCost.of_quiet code _ (DeleteFrame.Kind.push_quiet .branch code))

/-- Price all outcomes of the actual terminal value clears and collapse
at its reached graph. The physical path extent is a current-state bound,
to be amortized with copying/heap growth in the global accounting. -/
theorem branch_clear_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=3#64) (empty : property 0#64 0#64) :
    source.clock-(evaluateHOLFiniteState source branchClear).2.clock≤(model.pending.heap.toNat-pathLower)/8+40 := by
  rw [branch_clear_execute source key length limit nodeLower pathLower property model active tag]
  let post:=BranchValueUpdate.post source model.node 0#64 0#64
  obtain ⟨current,same,currentRegions,currentDisjoint,⟨currentValues⟩,currentPaths,currentPathRegions,currentSeparated,_buffer,storeFields,_storeMemory⟩:=
    branch_clear_memory source key length limit nodeLower pathLower property model active tag empty
  have args : evalListHOLFinite post (h:=fun query=>Classical.propDecidable (post.memaddrs query)) branchValueArguments=some [.val (.word model.node)]:=by
    simp [branchValueArguments,evalListHOLFinite,evalListHOLExact,localVar,evalHOLExact,toExact,show post.locals.lookup (ofString "node")=some (.val (.word model.node)) from model.nodeCell]
  have member : current.valid model.node:=by rw [same]; exact model.nodeMember
  have currentTag : wordAt post.memory model.node=3#64:=(storeFields.tags model.node model.nodeMember active).trans tag
  have floor : 2701131776≤pathLower:=(by decide : 2701131776≤DeleteFrame.ceiling).trans model.pending.floor
  obtain ⟨callee,called,calleeNode⟩:=CollapseBranch.environment post model.node (CollapseBranch.original_code post.code model.pending.installed)
  have priced:=CollapseBranch.body_cost (callEntryStateHOLFinite post callee) model.pending.heap model.node current limit nodeLower pathLower (model.pending.heap.toNat-pathLower) property currentValues currentRegions currentDisjoint
    currentPaths currentPathRegions currentSeparated (TrieWalk.Graph.PathLimit.of_regions current pathLower model.pending.heap.toNat currentPathRegions)
    (model.pending.pathFloor.trans model.pending.nodeFloor) floor member active currentTag calleeNode model.pending.heapCell model.pending.heapArena model.pending.heapAligned model.pending.little model.pending.scratch.domain model.pending.installed
  exact Input.ClockCost.assigned_current post (some (.local,ofString "res")) (ofString "_collapse_branch") branchValueArguments _ CollapseBranch.body callee .one
    ((model.pending.heap.toNat-pathLower)/8+39) args called priced

theorem branch_value_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=3#64) (empty : property 0#64 0#64) :
    source.clock-(evaluateHOLFiniteState source branchValue).2.clock≤(model.pending.heap.toNat-pathLower)/8+40 := by
  rw [branch_value_dispatch source key length limit nodeLower pathLower property model active tag]
  by_cases zero : wordAt source.memory (model.node+168#64)=0#64
  · rw [if_pos zero]
    exact (Input.ClockCost.assign source.code (ofString "res") (localVar "node") source rfl).trans (Nat.zero_le _)
  · rw [if_neg zero]
    exact branch_clear_cost source key length limit nodeLower pathLower property model active tag empty

theorem branch_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=3#64) (empty : property 0#64 0#64) :
    source.clock-(evaluateHOLFiniteState source branchBlock).2.clock≤(model.pending.heap.toNat-pathLower)/8+40 := by
  rw [branch_dispatch source key length limit nodeLower pathLower property model]
  by_cases done : model.level=length
  · rw [if_pos done]
    exact branch_value_cost source key length limit nodeLower pathLower property model active tag empty
  · rw [if_neg done]
    exact (branch_scope_price source.code model.pending.installed source rfl).trans (by omega)

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.branch_scope_price
#print axioms InitECandidate.Solver.Mpt.DeleteBody.branch_clear_cost
#print axioms InitECandidate.Solver.Mpt.DeleteBody.branch_value_cost
#print axioms InitECandidate.Solver.Mpt.DeleteBody.branch_cost
