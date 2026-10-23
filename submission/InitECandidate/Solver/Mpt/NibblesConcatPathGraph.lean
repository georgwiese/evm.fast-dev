import InitECandidate.Solver.Mpt.NibblesConcatNormal
import InitECandidate.Solver.Mpt.TriePathBufferPrefix
import InitECandidate.Solver.Mpt.TriePathBufferBounds

namespace InitECandidate.Solver.Mpt.NibblesConcat
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- Fresh concatenation retains the complete existing registry, including
shared or cyclic nodes, and provides a new buffer separated from every
mutable node. Allocation success comes from the original normal execution. -/
theorem body_path_graph (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap a al b bl : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat)
    (property : BitVec 64 → BitVec 64 → Prop) (values : TrieWalk.Values graph limit property)
    (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (left : graph.PathBuffer source.be pathLower heap.toNat a al.toNat)
    (right : graph.PathBuffer source.be pathLower heap.toNat b bl.toNat) (floor : 2701131776≤pathLower)
    (aCell : source.locals.lookup (ofString "a")=some (.val (.word a)))
    (alCell : source.locals.lookup (ofString "al")=some (.val (.word al)))
    (bCell : source.locals.lookup (ofString "b")=some (.val (.word b)))
    (blCell : source.locals.lookup (ofString "bl")=some (.val (.word bl)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    value=.val (.word heap) ∧
      target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (al+bl)))) ∧
      AllocatedBytes.Arena (PersistentAlloc.rounded heap (al+bl)) 0 ∧ (PersistentAlloc.rounded heap (al+bl)).toNat%8=0 ∧
      heap.toNat+al.toNat+bl.toNat≤(PersistentAlloc.rounded heap (al+bl)).toNat ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) ∧
      ∃ next : TrieWalk.Graph target.memory target.memaddrs,next.valid=graph.valid ∧
        next.Regions nodeLower (PersistentAlloc.rounded heap (al+bl)).toNat ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes target.be ∧
        next.PathRegions pathLower (PersistentAlloc.rounded heap (al+bl)).toNat ∧ next.PathSeparated ∧
        next.PathBuffer target.be pathLower (PersistentAlloc.rounded heap (al+bl)).toNat heap (al.toNat+bl.toNat) := by
  have sourceA : AllocatedBytes.Arena a al.toNat:=⟨floor.trans left.bounds.1,by have before:=left.bounds.2; have upper:=frontier.upper; omega⟩
  have sourceB : AllocatedBytes.Arena b bl.toNat:=⟨floor.trans right.bounds.1,by have before:=right.bounds.2; have upper:=frontier.upper; omega⟩
  obtain ⟨answer,frame,nextArena,nextAligned,grows,span,older⟩:=body_path_normal source target heap a al b bl left.span right.span sourceA sourceB left.bounds.2 right.bounds.2
    aCell alCell bCell blCell heapCell frontier aligned little domain installed value normal
  have fields:=Input.evaluation_fields source target body (some (.returned value)) normal
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  have heapResult : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (al+bl)))):=by
    change target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (al+bl)))) at globals
    rw [globals]
    simp [HolFiniteMapExact.update,FUPDATE]
  obtain ⟨next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    graph.after_path_prefix source target limit nodeLower pathLower heap.toNat property values regions disjoint paths pathRegions separated fields.1 fields.2.1 older
  have buffer:=TrieWalk.Graph.PathBuffer.fresh next target.be nodeLower heap.toNat (PersistentAlloc.rounded heap (al+bl)).toNat heap (al.toNat+bl.toNat)
    nextRegions aligned span (Nat.le_refl _) (by omega)
  refine ⟨answer,heapResult,nextArena,nextAligned,grows,older,next,same,?_,nextDisjoint,nextValues,nextPaths,?_,nextSeparated,?_⟩
  · intro node member active
    obtain ⟨lower,arena,alignment,before⟩:=nextRegions node member active
    exact ⟨lower,arena,alignment,by omega⟩
  · exact TrieWalk.Graph.PathRegions.weaken next pathLower heap.toNat pathLower (PersistentAlloc.rounded heap (al+bl)).toNat nextPathRegions (Nat.le_refl _) (by omega)
  · exact buffer.weaken next target.be heap.toNat (PersistentAlloc.rounded heap (al+bl)).toNat pathLower (PersistentAlloc.rounded heap (al+bl)).toNat heap (al.toNat+bl.toNat)
      (by have bounds:=left.bounds; omega) (Nat.le_refl _)

end InitECandidate.Solver.Mpt.NibblesConcat

#print axioms InitECandidate.Solver.Mpt.NibblesConcat.body_path_graph
