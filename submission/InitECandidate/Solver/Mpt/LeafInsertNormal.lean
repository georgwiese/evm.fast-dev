import InitECandidate.Solver.Mpt.LeafInsertAfterLength
import InitECandidate.Solver.Mpt.LeafInsertEntry

namespace InitECandidate.Solver.Mpt.InsertLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole original249 matching/splitting normal return. Every real node,
call and allocation is derived from the unchanged execution; all old nodes,
bounded values, full path bytes and their ownership survive. Older memory
below the node frontier survives both value replacement and fresh splitting. -/
theorem body_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key length pointer size : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (member : graph.valid node) (active : node≠0#64) (leaf : wordAt source.memory node=1#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "rk")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "rl")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (small : length.toNat≤64) (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧ source.clock-target.clock≤5*length.toNat+242 ∧
      (∀ query : BitVec 64,query.toNat<nodeLower → target.memory query=source.memory query) ∧
      (∀ current,graph.valid current → current≠0#64 → wordAt target.memory current=wordAt source.memory current) ∧
      ∃ finalHeap root : BitVec 64,value=.val (.word root) ∧ target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ current,graph.valid current → next.valid current) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
          graph.PathFields target.memory ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat → target.memory address=source.memory address) ∧
          (∀ current,next.valid current → graph.valid current ∨ heap.toNat≤current.toNat) ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat →
            TrieWalk.PathWordAway key length.toNat address → next.ProtectedWord address) := by
  obtain ⟨inner,continued,endpoint⟩:=field_entry_normal source target graph node member active leaf nodeCell value normal
  let ready:=fieldEntry source node
  have current (name : MlS) (notKey : name≠ofString "ek") (notLength : name≠ofString "el") : ready.locals.lookup name=source.locals.lookup name:=
    field_entry_lookup_other source node name notKey notLength
  obtain ⟨leftCell,oldLengthCell⟩:=field_entry_cells source node
  obtain ⟨domainEq,endianEq,codeEq,price,olderMemory,tags,finalHeap,root,answer,finalHeapCell,finalArena,finalAligned,grows,next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,fields,protectedWords,provenance,protection⟩:=
    after_length_path_normal ready inner heap node key length pointer size graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated query member active leaf
      ((current _ (by decide) (by decide)).trans nodeCell) leftCell oldLengthCell ((current _ (by decide) (by decide)).trans keyCell)
      ((current _ (by decide) (by decide)).trans lengthCell) ((current _ (by decide) (by decide)).trans pointerCell) ((current _ (by decide) (by decide)).trans sizeCell)
      payload extra floor empty domain heapCell frontier aligned installed small value continued
  rw [endpoint]
  exact ⟨domainEq,endianEq,codeEq,price,olderMemory,tags,finalHeap,root,answer,finalHeapCell,finalArena,finalAligned,grows,
    next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,fields,protectedWords,provenance,protection⟩

end InitECandidate.Solver.Mpt.InsertLeaf

#print axioms InitECandidate.Solver.Mpt.InsertLeaf.body_path_normal
