import InitECandidate.Solver.Mpt.DeleteDescentModel
import InitECandidate.Solver.Mpt.TrieInvalidateMemoryFrame
import InitECandidate.Solver.Mpt.TriePathFieldsMutation

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real descent invalidation changes only the current node's three
cache words. Its normally continuing call derives the exact memory and
retains the complete descent/pending-stack invariant and full query. -/
theorem invalidate_descent_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "node_invalidate") [localVar "node"])=(none,target)) :
    ∃ next : DescentModel target key length limit nodeLower pathLower property,
      next.pending.heap=model.pending.heap ∧ next.pending.cursor=model.pending.cursor ∧ next.pending.frame=model.pending.frame ∧
      next.pending.frames=model.pending.frames ∧ next.pending.graph.valid=model.pending.graph.valid ∧
      next.node=model.node ∧ next.level=model.level ∧ next.go=model.go ∧
      model.pending.graph.PathFields target.memory ∧
      (∀ query : BitVec 64,query.toNat<nodeLower→target.memory query=source.memory query) ∧ source.clock-target.clock≤1 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [localVar "node"]=some [.val (.word model.node)]:=by
    simp [evalListHOLFinite,evalListHOLExact,localVar,evalHOLExact,toExact,model.nodeCell]
  obtain ⟨targetEq,current,same,currentRegions,currentDisjoint,⟨currentValues⟩,currentPaths,currentPathRegions,currentSeparated,buffer⟩:=
    model.pending.graph.invalidate_call_paths source target model.node key length.toNat limit nodeLower model.pending.heap.toNat pathLower model.pending.heap.toNat property
      model.pending.values model.pending.regions model.pending.disjoint model.pending.paths model.pending.pathRegions model.pending.separated model.query model.nodeMember active
      [localVar "node"] args model.pending.installed model.pending.scratch.domain normal
  have fields:=TrieWalk.Graph.PathFields.of_invalidate source model.node model.pending.graph nodeLower model.pending.heap.toNat model.pending.regions model.pending.disjoint model.nodeMember active
  have older:=(model.pending.graph.invalidate_memory_frames source model.node nodeLower model.pending.heap.toNat model.pending.regions model.pending.disjoint model.nodeMember active).1
  subst target
  let afterState:={NodeInvalidate.post source model.node with clock:=source.clock-1}
  let pending : UnwindModel afterState limit nodeLower pathLower property := {
    heap:=model.pending.heap
    cursor:=model.pending.cursor
    frame:=model.pending.frame
    top:=model.pending.top
    result:=model.pending.result
    frames:=model.pending.frames
    topCell:=model.pending.topCell
    resultCell:=model.pending.resultCell
    heapCell:=model.pending.heapCell
    heapArena:=model.pending.heapArena
    heapAligned:=model.pending.heapAligned
    scratch:=model.pending.scratch.of_fields source afterState model.pending.cursor model.pending.frame rfl rfl
    scratchBefore:=model.pending.scratchBefore
    floor:=model.pending.floor
    pathFloor:=model.pending.pathFloor
    nodeFloor:=model.pending.nodeFloor
    little:=model.pending.little
    installed:=model.pending.installed
    graph:=current
    resultMember:=by rw [same]; exact model.pending.resultMember
    values:=currentValues
    regions:=currentRegions
    disjoint:=currentDisjoint
    paths:=currentPaths
    pathRegions:=currentPathRegions
    separated:=currentSeparated
    stack:=model.pending.stack.of_before source afterState model.pending.cursor.toNat nodeLower model.pending.top model.pending.frames
      (model.pending.floor.trans model.pending.pathFloor) older
    parents:=model.pending.parents.of_fields model.pending.graph current model.pending.frames (by intro node member; rw [same]; exact member) fields
    bounded:=model.pending.bounded }
  let next : DescentModel afterState key length limit nodeLower pathLower property := {
    pending:=pending
    node:=model.node
    level:=model.level
    go:=model.go
    keyCell:=model.keyCell
    lengthCell:=model.lengthCell
    nodeCell:=model.nodeCell
    levelCell:=model.levelCell
    goCell:=model.goCell
    goTyped:=model.goTyped
    bounded:=model.bounded
    levelBound:=model.levelBound
    depthBound:=model.depthBound
    nodeMember:=by rw [same]; exact model.nodeMember
    query:=buffer }
  exact ⟨next,rfl,rfl,rfl,rfl,same,rfl,rfl,rfl,fields,older,(by change source.clock-(source.clock-1)≤1; omega)⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.invalidate_descent_normal
