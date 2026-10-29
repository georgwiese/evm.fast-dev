import InitECandidate.Solver.Mpt.InsertBranchScopeNormal
import InitECandidate.Solver.Mpt.InsertBranchValueNormal
import InitECandidate.Solver.Mpt.InsertNodeOutputTerminal
import InitECandidate.Solver.Mpt.InsertNodeOutputDescend
import InitECandidate.Solver.Mpt.InsertPending
import InitECandidate.Solver.Mpt.TrieProtectedMutation
import InitECandidate.Solver.Mpt.TriePathFieldsMutation

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Both real original branch cases, packaged at the actual dispatch exit. -/
theorem branch_output_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key level length pointer size : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (pending : Pending source) (member : graph.valid node) (active : node≠0#64)
    (notHash : wordAt source.memory node≠0#64) (notLeaf : wordAt source.memory node≠1#64) (notExtension : wordAt source.memory node≠2#64)
    (nodeClean : TrieWalk.Uncached source.memory node)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (before : level.toNat≤length.toNat) (bounded : length.toNat≤64)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (normal : evaluateHOLFiniteState source branchChoice=(none,target)) :
    Nonempty (NodeOutput source target graph heap key length level limit nodeLower pathLower property) := by
  by_cases equal : level=length
  · have selected : evaluateHOLFiniteState source branchChoice=evaluateHOLFiniteState source branchValue:=by
      rw [branch_shapes.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,levelCell,lengthCell,equal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    obtain ⟨endpoint,memory,tags,next,same,nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated,buffers⟩:=
      branch_value_normal source target node pointer size graph limit nodeLower heap.toNat pathLower heap.toNat property values regions disjoint paths pathRegions separated
        member active notHash notLeaf notExtension nodeCell pointerCell sizeCell payload extra (selected.symm.trans normal)
    have localsEq : target.locals=source.locals.update (ofString "r",.val (.word node)):=by rw [endpoint]; rfl
    exact terminal_output source target heap key length level node heap graph limit nodeLower pathLower property pending.node pending.slot pending.level pending.go localsEq
      (by rw [endpoint]; rfl) (by rw [endpoint]; rfl) (by rw [endpoint]; rfl) (by rw [endpoint]; exact heapCell) frontier aligned (Nat.le_refl _) memory
      (by
        rw [endpoint]
        apply TrieWalk.Graph.PathFields.of_agreement graph
        intro address needed
        have away:=graph.branch_value_away nodeLower heap.toNat regions disjoint node address member active notHash notLeaf notExtension needed
        exact BranchValueUpdate.post_away source node pointer size address away.1 away.2)
      (by
        intro address safe _before
        rw [endpoint]
        exact BranchValueUpdate.post_away source node pointer size address
          (safe.nodes node member active 160 (by simp [TrieWalk.nodeBytes,notHash,notLeaf,notExtension]))
          (safe.nodes node member active 168 (by simp [TrieWalk.nodeBytes,notHash,notLeaf,notExtension])))
      tags next (by intro current live; rw [same]; exact live) (by rw [same]; exact member) nextValues nextRegions nextDisjoint nextPaths nextPathRegions nextSeparated
      (by intro current live; exact Or.inl (by rwa [same] at live))
      (by
        intro address safe _before _away
        apply safe.of_fields graph next address same
        rw [endpoint]
        exact TrieWalk.Graph.PathFields.of_branch_value source node pointer size graph nodeLower heap.toNat regions disjoint member active notHash notLeaf notExtension)
      (by
        rw [endpoint]
        exact graph.cache_branch_value_of_tags source nodeLower heap.toNat regions disjoint node pointer size member active notHash notLeaf notExtension)
      (by
        rw [endpoint]
        exact (graph.cache_branch_value_of_tags source nodeLower heap.toNat regions disjoint node pointer size member active notHash notLeaf notExtension).uncached graph node member nodeClean)
  · have strict : level.toNat<length.toNat:=by
      have different : level.toNat≠length.toNat:=by intro same; exact equal (BitVec.toNat_inj.mp same)
      omega
    have selected : evaluateHOLFiniteState source branchChoice=evaluateHOLFiniteState source branchDescendScope:=by
      rw [branch_shapes.1,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,toExact,localVar,levelCell,lengthCell,equal,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    obtain ⟨index,small,child,childMember,slot,addition,nextBound,endpoint⟩:=branch_scope_normal source target node key level length graph member active notHash notLeaf notExtension
      query.span nodeCell keyCell levelCell strict bounded (selected.symm.trans normal)
    exact descend_output source target heap key length level node child (node+32#64+BitVec.ofNat 64 (index*8)) (level+1#64)
      graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated query member childMember slot
      (by rw [addition]; omega) nextBound heapCell frontier aligned nodeClean endpoint

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.branch_output_normal
