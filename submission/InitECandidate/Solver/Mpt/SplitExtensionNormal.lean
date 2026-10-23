import InitECandidate.Solver.Mpt.SplitExtensionBranchNormal
import InitECandidate.Solver.Mpt.SplitExtensionEntry

namespace InitECandidate.Solver.Mpt.SplitExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole unchanged250 derives its real loaded fields, fresh branch,
old/new child construction and stores. Every old graph node, bounded value
and full protected path survives; the actual return is the fresh branch. -/
theorem body_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key length prefixLength pointer size : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=2#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "rk")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "rl")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (prefixCell : source.locals.lookup (ofString "pl")=some (.val (.word prefixLength)))
    (strict : prefixLength.toNat<(wordAt source.memory (node+40#64)).toNat)
    (queryBound : prefixLength.toNat≤length.toNat)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    value=.val (.word heap) ∧ target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) ∧
      ∃ finalHeap : BitVec 64,target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧ wordAt target.memory heap=3#64 ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,
          (∀ node,graph.valid node → next.valid node) ∧ next.valid heap ∧ next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧
          Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated := by
  obtain ⟨inner,continued,endpoint⟩:=field_entry_normal source target graph node member active tag nodeCell value normal
  let ready:=fieldEntry source node
  have current (name : MlS) (notSegment : name≠ofString "seg") (notLength : name≠ofString "sl") (notChild : name≠ofString "child") :
      ready.locals.lookup name=source.locals.lookup name:=field_entry_lookup_other source node name notSegment notLength notChild
  obtain ⟨segmentCell,oldLengthCell,childCell⟩:=field_entry_cells source node
  have buffer:=TrieWalk.Graph.PathBuffer.stored graph source.be pathLower heap.toNat paths pathRegions separated node member active (Or.inr tag)
  have childMember:=stored_child_member source graph node member active tag
  obtain ⟨answer,domainEq,endianEq,codeEq,memory,finalHeap,finalHeapCell,finalArena,finalAligned,grows,finalTag,next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    branch_scope_normal ready inner heap (wordAt source.memory (node+32#64)) prefixLength (wordAt source.memory (node+40#64)) (wordAt source.memory (node+48#64)) key length pointer size
      graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated buffer query queryBound
      ((current _ (by decide) (by decide) (by decide)).trans keyCell) ((current _ (by decide) (by decide) (by decide)).trans lengthCell)
      ((current _ (by decide) (by decide) (by decide)).trans pointerCell) ((current _ (by decide) (by decide) (by decide)).trans sizeCell)
      payload extra strict floor empty segmentCell ((current _ (by decide) (by decide) (by decide)).trans prefixCell) oldLengthCell childCell childMember
      domain heapCell frontier aligned installed value continued
  rw [endpoint]
  exact ⟨answer,domainEq,endianEq,codeEq,memory,finalHeap,finalHeapCell,finalArena,finalAligned,grows,finalTag,next,members,rootMember,
    nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩

end InitECandidate.Solver.Mpt.SplitExtension

#print axioms InitECandidate.Solver.Mpt.SplitExtension.body_path_normal
