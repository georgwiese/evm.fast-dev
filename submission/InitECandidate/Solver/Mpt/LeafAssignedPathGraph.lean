import InitECandidate.Solver.Mpt.LeafConstructorCall
import InitECandidate.Solver.Mpt.LeafConstructorPathGraph

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- An actual assigned leaf call registers its borrowed full path and
bounded value, including a suffix at a nonzero insertion level. -/
theorem leaf_assigned_paths (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap key length pointer size : BitVec 64) (name : MlS) (arguments : List (ExpHOL 64))
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size) (floor : nodeLower≤heap.toNat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word key),.val (.word length),.val (.word pointer),.val (.word size)])
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "node_new_leaf") arguments)=(none,target)) :
    target.locals=source.locals.update (name,.val (.word heap)) ∧ target.code=source.code ∧ source.clock-target.clock≤2 ∧
      Physical .leaf source target heap (leafWords key length pointer size) ∧
      ∃ next : TrieWalk.Graph target.memory target.memaddrs,
        (∀ node,next.valid node ↔ graph.valid node ∨ node=heap) ∧ next.valid heap ∧
        next.Regions nodeLower (PersistentAlloc.rounded heap 64#64).toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
        next.PathBytes target.be ∧ next.PathRegions pathLower (PersistentAlloc.rounded heap 64#64).toNat ∧ next.PathSeparated := by
  obtain ⟨arena,endpoint⟩:=leaf_assigned source target heap key length pointer size name arguments args domain heapCell frontier aligned installed normal
  have physical : Physical .leaf source target heap (leafWords key length pointer size):=
    physical_of_fields .leaf source target heap (leafWords key length pointer size) arena aligned
      (by rw [endpoint]; rfl) (by rw [endpoint]; rfl) (by rw [endpoint]; rfl) (by rw [endpoint]; rfl)
  have localsEq : target.locals=source.locals.update (name,.val (.word heap)):=by rw [endpoint]; rfl
  have codeEq : target.code=source.code:=by rw [endpoint]; rfl
  have clockEq : target.clock=source.clock-2:=by rw [endpoint]; rfl
  refine ⟨localsEq,codeEq,by rw [clockEq]; omega,physical,?_⟩
  exact physical.leaf_path_graph source target heap (leafWords key length pointer size) domain aligned graph limit nodeLower pathLower property
    values regions disjoint paths pathRegions separated floor (by simpa [leafWords] using buffer)
      (by simpa [leafWords] using payload) (by simpa [leafWords] using extra)

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.leaf_assigned_paths
