import InitECandidate.Solver.Mpt.CollapseBranchDispatch
import InitECandidate.Solver.Mpt.CollapseBranchEmptyNormal
import InitECandidate.Solver.Mpt.CollapseBranchSingleNormal
import InitECandidate.Solver.Mpt.CollapseBranchValueModel

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- All three actual post-scan collapse choices. The only possible added
node is the real returned root, which is old or fresh above the entry heap.
Every word below that heap survives, including independent caller tables. -/
theorem choices_paths (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap node : BitVec 64) (model : ScanModel source node)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (floor : 2701131776≤pathLower) (pathFloor : pathLower≤nodeLower) (nodeFloor : nodeLower≤heap.toNat)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=3#64)
    (valueCell : source.locals.lookup (ofString "vl")=some (.val (.word (wordAt source.memory (node+168#64)))))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterValue=(some (.returned value),target)) :
    target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) ∧
      ∃ root finalHeap : BitVec 64,value=.val (.word root) ∧ target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧ (graph.valid root ∨ heap.toNat≤root.toNat) ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ current,next.valid current ↔ graph.valid current ∨ current=root) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated := by
  rw [after_value_dispatch source model.count _ model.countCell valueCell] at normal
  by_cases empty : model.count=0#64
  · rw [if_pos empty] at normal
    obtain ⟨answer,_price,code,physical,next,members,root,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
      empty_paths source target heap node graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated pathFloor nodeFloor member active tag model.nodeCell
        valueCell heapCell frontier aligned domain installed value normal
    have grows : heap.toNat≤(PersistentAlloc.rounded heap 64#64).toNat:=by
      have before:=physical.before
      change heap.toNat+64≤(PersistentAlloc.rounded heap 64#64).toNat at before
      omega
    exact ⟨physical.domain,physical.endian,code,fun query before=>physical.memory query (Or.inl before),heap,PersistentAlloc.rounded heap 64#64,answer,physical.heapCell,
      physical.nextArena,physical.nextAligned,grows,Or.inr (Nat.le_refl _),next,members,root,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩
  · rw [if_neg empty] at normal
    by_cases single : model.count=1#64 ∧ wordAt source.memory (node+168#64)=0#64
    · rw [if_pos single] at normal
      have positiveCount : model.count≠0#64:=by rw [single.1]; decide
      obtain ⟨domainEq,endianEq,codeEq,older,child,root,finalHeap,_childMember,_childActive,_notHash,_price,answer,finalCell,finalArena,finalAligned,fresh,grows,
        next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
        single_paths source target heap node model.selectedIndex graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated (pathFloor.trans nodeFloor) floor nodeFloor
          member active tag model.nodeCell model.indexCell model.indexBound (model.selectedNonzero positiveCount) heapCell frontier aligned little domain installed value normal
      exact ⟨domainEq,endianEq,codeEq,older,root,finalHeap,answer,finalCell,finalArena,finalAligned,fresh.trans grows,Or.inr fresh,
        next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩
    · rw [if_neg single,value_shapes.2.2.2.2.2.2.2.2] at normal
      obtain ⟨read,endpoint⟩:=Input.return_normal source target (localVar "node") value normal
      have expected : eval source (localVar "node")=some (.val (.word node)):=by simp [eval,localVar,evalHOLExact,toExact,model.nodeCell]
      have answer : value=.val (.word node):=Option.some.inj (read.symm.trans expected)
      rw [endpoint]
      refine ⟨rfl,rfl,rfl,fun _ _=>rfl,node,heap,answer,heapCell,frontier,aligned,Nat.le_refl _,Or.inl member,graph,?_,member,regions,disjoint,⟨values⟩,paths,pathRegions,separated⟩
      intro current
      constructor
      · exact Or.inl
      · intro actual
        rcases actual with old|same
        · exact old
        · rwa [same]

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.choices_paths
