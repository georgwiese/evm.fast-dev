import InitECandidate.Solver.Mpt.DeleteExtensionTailArguments
import InitECandidate.Solver.Mpt.LeafConstructorTail
import InitECandidate.Solver.Mpt.ExtensionConstructorTail
import InitECandidate.Solver.Mpt.LeafConstructorPathGraph
import InitECandidate.Solver.Mpt.ExtensionConstructorPathGraph
import InitECandidate.Solver.Mpt.NodeConstructorProtected

namespace InitECandidate.Solver.Mpt.DeleteExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original merge footer constructs a leaf or positive extension
over the real joined buffer. Both real tail calls derive their allocation,
registered result and complete graph/path contract from normal execution. -/
theorem constructor_paths (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap child key length : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat key length.toNat) (positive : 0<length.toNat) (floor : nodeLower≤heap.toNat)
    (member : graph.valid child) (active : child≠0#64) (tag : wordAt source.memory child=1#64 ∨ wordAt source.memory child=2#64)
    (keyCell : source.locals.lookup (ofString "cat")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "cl")=some (.val (.word length)))
    (childCell : source.locals.lookup (ofString "nc")=some (.val (.word child)))
    (tagCell : source.locals.lookup (ofString "ck")=some (.val (.word (wordAt source.memory child))))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (domain : source.memaddrs=InitE.ordinaryDomain)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterLength=(some (.returned value),target)) :
    value=.val (.word heap) ∧ target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧ source.clock-target.clock≤3 ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) ∧
      ∃ finalHeap : BitVec 64,target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ node,next.valid node ↔ graph.valid node ∨ node=heap) ∧ next.valid heap ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat →
            TrieWalk.PathWordAway key length.toNat address → next.ProtectedWord address) := by
  by_cases extension : wordAt source.memory child=2#64
  · rw [constructor_dispatch source _ tagCell,if_pos extension] at normal
    obtain ⟨grandchild,args⟩:=extension_arguments source child key length graph member active extension keyCell lengthCell childCell
    obtain ⟨answer,physical,code,price⟩:=NodeConstructor.extension_tail_physical source target heap key length (wordAt source.memory (child+48#64)) extensionArguments
      args domain heapCell frontier aligned installed value normal
    obtain ⟨next,same,root,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=physical.extension_path_graph source target heap
      (NodeConstructor.extensionWords key length (wordAt source.memory (child+48#64))) domain aligned graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated floor
        (by simpa [NodeConstructor.extensionWords] using buffer) (by simpa [NodeConstructor.extensionWords] using grandchild) (by simpa [NodeConstructor.extensionWords] using positive)
    have grows : heap.toNat≤(PersistentAlloc.rounded heap 56#64).toNat:=by have before:=physical.before; change heap.toNat+56≤(PersistentAlloc.rounded heap 56#64).toNat at before; omega
    exact ⟨answer,physical.domain,physical.endian,code,price,fun query before=>physical.memory query (Or.inl before),
      PersistentAlloc.rounded heap 56#64,physical.heapCell,physical.nextArena,physical.nextAligned,grows,next,same,root,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,
      (by
        intro address safe before away
        exact (physical.path_protected .extension (Or.inr rfl) source target heap _ graph next nodeLower regions same address safe before
          (by simpa [NodeConstructor.extensionWords] using away)).2)⟩
  · have leaf:=tag.resolve_right extension
    rw [constructor_dispatch source _ tagCell,if_neg extension,merge_shapes.2.2.2.2.2.2] at normal
    obtain ⟨payload,extra,args⟩:=leaf_arguments source child key length graph limit property values member active leaf keyCell lengthCell childCell
    obtain ⟨answer,physical,code,price⟩:=NodeConstructor.leaf_tail_physical source target heap key length (wordAt source.memory (child+48#64)) (wordAt source.memory (child+56#64))
      leafArguments args domain heapCell frontier aligned installed value normal
    obtain ⟨next,same,root,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=physical.leaf_path_graph source target heap
      (NodeConstructor.leafWords key length (wordAt source.memory (child+48#64)) (wordAt source.memory (child+56#64))) domain aligned graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated floor
        (by simpa [NodeConstructor.leafWords] using buffer) (by simpa [NodeConstructor.leafWords] using payload) (by simpa [NodeConstructor.leafWords] using extra)
    have grows : heap.toNat≤(PersistentAlloc.rounded heap 64#64).toNat:=by have before:=physical.before; change heap.toNat+64≤(PersistentAlloc.rounded heap 64#64).toNat at before; omega
    exact ⟨answer,physical.domain,physical.endian,code,price,fun query before=>physical.memory query (Or.inl before),
      PersistentAlloc.rounded heap 64#64,physical.heapCell,physical.nextArena,physical.nextAligned,grows,next,same,root,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,
      (by
        intro address safe before away
        exact (physical.path_protected .leaf (Or.inl rfl) source target heap _ graph next nodeLower regions same address safe before
          (by simpa [NodeConstructor.leafWords] using away)).2)⟩

end InitECandidate.Solver.Mpt.DeleteExtension

#print axioms InitECandidate.Solver.Mpt.DeleteExtension.constructor_paths
