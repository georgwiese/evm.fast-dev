import InitECandidate.Solver.Mpt.CollapseBranchBranchTail
import InitECandidate.Solver.Mpt.CollapseBranchMergeNormal
import InitECandidate.Solver.Mpt.TrieGraphKinds

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def afterStorePrice (memory : Memory) (child : BitVec 64) : Nat:=
  if wordAt memory child=3#64 then 3 else (wordAt memory (child+40#64)).toNat/8+22

/-- Complete original suffix after the fresh selected nibble. The branch
child case uses no path copy; leaf/extension cases use the real full path.
Only the actual returned constructor node enlarges the old registry. -/
theorem after_store_paths (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nibble child : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat nibble 1) (floor : 2701131776≤pathLower) (nodeFloor : nodeLower≤heap.toNat)
    (member : graph.valid child) (active : child≠0#64) (notHash : wordAt source.memory child≠0#64)
    (nibbleCell : source.locals.lookup (ofString "nib")=some (.val (.word nibble)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (tagCell : source.locals.lookup (ofString "ck")=some (.val (.word (wordAt source.memory child))))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterStore=(some (.returned value),target)) :
    target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧ source.clock-target.clock≤afterStorePrice source.memory child ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) ∧
      ∃ root finalHeap : BitVec 64,value=.val (.word root) ∧ target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤root.toNat ∧ root.toNat≤finalHeap.toNat ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ node,next.valid node ↔ graph.valid node ∨ node=root) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated := by
  by_cases branch : wordAt source.memory child=3#64
  · have currentTag : source.locals.lookup (ofString "ck")=some (.val (.word 3#64)):=by simpa only [branch] using tagCell
    obtain ⟨answer,price,code,physical,next,members,root,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
      branch_tail_paths source target heap nibble child graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated buffer nodeFloor member
        nibbleCell childCell currentTag heapCell frontier aligned domain installed value normal
    have grows : heap.toNat≤(PersistentAlloc.rounded heap 56#64).toNat:=by
      have before:=physical.before
      change heap.toNat+56≤(PersistentAlloc.rounded heap 56#64).toNat at before
      omega
    exact ⟨physical.domain,physical.endian,code,(by simpa only [afterStorePrice,if_pos branch] using price),fun query before=>physical.memory query (Or.inl before),
      heap,PersistentAlloc.rounded heap 56#64,answer,physical.heapCell,physical.nextArena,physical.nextAligned,Nat.le_refl _,grows,
      next,members,root,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩
  · have pathTag:=graph.path_kind child member active notHash branch
    rw [branch_dispatch source _ tagCell,if_neg branch] at normal
    obtain ⟨domainEq,endianEq,codeEq,price,older,root,finalHeap,answer,finalCell,finalArena,finalAligned,fresh,grows,
      next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
      merge_paths source target heap nibble child graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated buffer floor nodeFloor member active pathTag
        nibbleCell childCell tagCell heapCell frontier aligned little domain installed value normal
    exact ⟨domainEq,endianEq,codeEq,(by simpa only [afterStorePrice,if_neg branch] using price),older,root,finalHeap,answer,finalCell,finalArena,finalAligned,fresh,grows,
      next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.after_store_paths
