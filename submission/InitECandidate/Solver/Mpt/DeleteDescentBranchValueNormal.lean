import InitECandidate.Solver.Mpt.DeleteDescentBranchValueMemory
import InitECandidate.Solver.Mpt.DeleteDescentChoiceOutput
import InitECandidate.Solver.Mpt.DeleteDescentPure
import InitECandidate.Solver.Mpt.DeleteDescentOutputPure
import InitECandidate.Solver.Mpt.CollapseBranchAssigned
import InitECandidate.Solver.Mpt.TriePathBufferGrowth

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Execute the actual zero-value writes, then original252 at its real
reached graph. The returned root, possible fresh node and preserved full
query are all derived from that genuinely continuing assigned call. -/
theorem branch_clear_output (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=3#64) (empty : property 0#64 0#64) (stopped : model.go=0#64)
    (normal : evaluateHOLFiniteState source branchClear=(none,target)) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) := by
  rw [branch_clear_execute source key length limit nodeLower pathLower property model active tag] at normal
  let post:=BranchValueUpdate.post source model.node 0#64 0#64
  obtain ⟨current,same,currentRegions,currentDisjoint,⟨currentValues⟩,currentPaths,currentPathRegions,currentSeparated,buffer,storeFields,storeMemory⟩:=
    branch_clear_memory source key length limit nodeLower pathLower property model active tag empty
  have args : evalListHOLFinite post (h:=fun query=>Classical.propDecidable (post.memaddrs query)) branchValueArguments=some [.val (.word model.node)]:=by
    simp [branchValueArguments,evalListHOLFinite,evalListHOLExact,localVar,evalHOLExact,toExact,show post.locals.lookup (ofString "node")=some (.val (.word model.node)) from model.nodeCell]
  have currentMember : current.valid model.node:=by rw [same]; exact model.nodeMember
  have currentTag : wordAt post.memory model.node=3#64:=(storeFields.tags model.node model.nodeMember active).trans tag
  have floor : 2701131776≤pathLower:=(by decide : 2701131776≤DeleteFrame.ceiling).trans model.pending.floor
  obtain ⟨root,localsEq,domainEq,endianEq,codeEq,_price,globalsEq,helperMemory,helperFields,finalHeap,finalCell,finalArena,finalAligned,grows,fresh,
    next,members,rootMember,nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated,_protection⟩:=
    CollapseBranch.assigned_path_normal post target model.pending.heap model.node current limit nodeLower pathLower property currentValues currentRegions currentDisjoint currentPaths currentPathRegions currentSeparated
      floor model.pending.pathFloor model.pending.nodeFloor currentMember active currentTag model.pending.heapCell model.pending.heapArena model.pending.heapAligned model.pending.little model.pending.scratch.domain model.pending.installed
      (ofString "res") branchValueArguments args normal
  have nextProvenance (node : BitVec 64) (member : next.valid node) : current.valid node ∨ model.pending.heap.toNat≤node.toNat:=by
    rcases (members node).1 member with old|equal
    · exact Or.inl old
    · rw [equal]; exact fresh
  have nextQuery:=buffer.of_growing_prefix post target current next pathLower model.pending.heap.toNat finalHeap.toNat nodeLower key length.toNat
    currentRegions nextRegions nextProvenance grows domainEq endianEq helperMemory
  have fields : model.pending.graph.PathFields target.memory:=storeFields.trans model.pending.graph current helperFields
    (by intro node member; rw [same]; exact member)
  have memory (address : BitVec 64) (before : address.toNat<nodeLower) : target.memory address=source.memory address:=
    (helperMemory address (before.trans_le model.pending.nodeFloor)).trans (storeMemory address before)
  have sourceFresh : model.pending.graph.valid root ∨ model.pending.heap.toNat≤root.toNat:=by
    rcases fresh with old|above
    · exact Or.inl (by rwa [same] at old)
    · exact Or.inr above
  let output : ChoiceOutput source target model.pending.graph model.pending.heap limit nodeLower pathLower property := {
    root:=root
    finalHeap:=finalHeap
    locals:=localsEq
    domain:=domainEq
    endian:=endianEq
    code:=codeEq
    globals:=globalsEq
    memory:=memory
    fields:=fields
    heapCell:=finalCell
    heapArena:=finalArena
    heapAligned:=finalAligned
    grows:=grows
    fresh:=sourceFresh
    next:=next
    members:=by intro node; rw [members node,same]
    rootMember:=rootMember
    regions:=nextRegions
    disjoint:=nextDisjoint
    values:=nextValues
    paths:=nextPaths
    pathRegions:=nextPathRegions
    separated:=nextSeparated }
  exact DescentOutput.of_choice source target key length limit nodeLower pathLower property model output nextQuery stopped

/-- Whole terminal branch-value choice. An already empty value keeps
the current registered node; a nonempty value is genuinely cleared and
collapsed while retaining the current query, ancestors and low cursors. -/
theorem branch_value_output (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=3#64) (empty : property 0#64 0#64) (stopped : model.go=0#64)
    (normal : evaluateHOLFiniteState source branchValue=(none,target)) :
    Nonempty (DescentOutput source target key length limit nodeLower pathLower property model) := by
  rw [branch_value_dispatch source key length limit nodeLower pathLower property model active tag] at normal
  by_cases zero : wordAt source.memory (model.node+168#64)=0#64
  · rw [if_pos zero] at normal
    have read : eval source (localVar "node")=some (.val (.word model.node)):=by simp [eval,localVar,evalHOLExact,toExact,model.nodeCell]
    have actual:=assign_result_execute source key length limit nodeLower pathLower property model (localVar "node") model.node read
    have endpoint : target=QueryBranch.bind source "res" model.node:=congrArg Prod.snd (normal.symm.trans actual)
    rw [endpoint]
    exact DescentOutput.of_erase source (QueryBranch.bind source "res" model.node) key length limit nodeLower pathLower property model
      (model.bind_result source key length limit nodeLower pathLower property model.node model.nodeMember) rfl rfl rfl rfl stopped rfl
  · rw [if_neg zero] at normal
    exact branch_clear_output source target key length limit nodeLower pathLower property model active tag empty stopped normal

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.branch_clear_output
#print axioms InitECandidate.Solver.Mpt.DeleteBody.branch_value_output
