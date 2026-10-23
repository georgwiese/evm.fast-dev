import InitECandidate.Solver.Mpt.SplitExtensionProgram
import InitECandidate.Solver.Mpt.NodeConstructorScoped
import InitECandidate.Solver.Mpt.BranchConstructorPathGraph
import InitECandidate.Solver.Mpt.TriePathBufferMutation
import InitECandidate.Solver.Mpt.TriePathBufferBounds

namespace InitECandidate.Solver.Mpt.SplitExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original250 branch scope supplies its genuine fresh branch,
closed graph and both full independent buffers at the real continuation. -/
theorem branch_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap key1 length1 key2 length2 : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (firstBuffer : graph.PathBuffer source.be pathLower heap.toNat key1 length1.toNat)
    (secondBuffer : graph.PathBuffer source.be pathLower heap.toNat key2 length2.toNat)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source branchScope=(some (.returned value),post)) :
    ∃ ready inner,ready.locals.lookup (ofString "br")=some (.val (.word heap)) ∧
      ready.locals=source.locals.update (ofString "br",.val (.word heap)) ∧
      NodeConstructor.BranchPhysical source ready heap ∧ ready.code=source.code ∧
      evaluateHOLFiniteState ready afterBranch=(some (.returned value),inner) ∧ post=restore source "br" inner ∧
      ∃ next : TrieWalk.Graph ready.memory ready.memaddrs,
        (∀ node,next.valid node ↔ graph.valid node ∨ node=heap) ∧ next.valid heap ∧
        next.Regions nodeLower (PersistentAlloc.rounded heap 176#64).toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
        next.PathBytes ready.be ∧ next.PathRegions pathLower (PersistentAlloc.rounded heap 176#64).toNat ∧ next.PathSeparated ∧
        next.PathBuffer ready.be pathLower (PersistentAlloc.rounded heap 176#64).toNat key1 length1.toNat ∧
        next.PathBuffer ready.be pathLower (PersistentAlloc.rounded heap 176#64).toNat key2 length2.toNat := by
  have called : evaluateHOLFiniteState source (.decCall (ofString "br") .one (ofString "node_new_branch") [] afterBranch)=(some (.returned value),post):=by
    rw [←entry_shapes.2.2.2.1]
    exact normal
  obtain ⟨funded,ready,inner,branchCell,localsEq,physical,codeEq,continued,endpoint⟩:=NodeConstructor.branch_scoped_physical source post heap "br" afterBranch
    domain heapCell frontier aligned installed value called
  obtain ⟨next,members,member,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    physical.path_graph source ready heap domain aligned graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated floor empty
  have actualTag : wordAt ready.memory heap=3#64:=by simp [wordAt,physical.tag,MemoryBytes.wordBits]
  have arena : AllocatedBytes.Arena heap (TrieWalk.nodeBytes (wordAt ready.memory heap)):=by
    simpa [actualTag,TrieWalk.nodeBytes,NodeConstructor.bytes] using physical.allocation.arena
  have grows : heap.toNat≤(PersistentAlloc.rounded heap 176#64).toNat:=by
    have before : heap.toNat+176≤(PersistentAlloc.rounded heap 176#64).toNat:=physical.allocation.before
    omega
  have memory : ∀ query : BitVec 64,query.toNat<heap.toNat → ready.memory query=source.memory query:=
    fun query before=>physical.allocation.memory query (Or.inl before)
  have first:=firstBuffer.after_fresh_node source ready graph next nodeLower pathLower heap key1 length1.toNat regions
    (fun node live=>(members node).mp live) arena physical.allocation.domain physical.allocation.endian memory
  have second:=secondBuffer.after_fresh_node source ready graph next nodeLower pathLower heap key2 length2.toNat regions
    (fun node live=>(members node).mp live) arena physical.allocation.domain physical.allocation.endian memory
  exact ⟨ready,inner,branchCell,localsEq,physical,codeEq,continued,endpoint,next,members,member,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,
    first.weaken next ready.be pathLower heap.toNat pathLower (PersistentAlloc.rounded heap 176#64).toNat key1 length1.toNat (Nat.le_refl _) grows,
    second.weaken next ready.be pathLower heap.toNat pathLower (PersistentAlloc.rounded heap 176#64).toNat key2 length2.toNat (Nat.le_refl _) grows⟩

end InitECandidate.Solver.Mpt.SplitExtension

#print axioms InitECandidate.Solver.Mpt.SplitExtension.branch_entry
