import InitECandidate.Solver.Mpt.ExtensionConstructorTail
import InitECandidate.Solver.Mpt.ExtensionConstructorPathGraph

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- An actual assigned extension call registers its positive borrowed
path and genuine child while preserving every older node and path. -/
theorem extension_assigned_paths (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap key length child : BitVec 64) (name : MlS) (arguments : List (ExpHOL 64))
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (childMember : graph.valid child) (positive : 0<length.toNat) (floor : nodeLower≤heap.toNat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      some [.val (.word key),.val (.word length),.val (.word child)])
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString "node_new_ext") arguments)=(none,target)) :
    target.locals=source.locals.update (name,.val (.word heap)) ∧ target.code=source.code ∧ source.clock-target.clock≤2 ∧
      Physical .extension source target heap (extensionWords key length child) ∧
      ∃ next : TrieWalk.Graph target.memory target.memaddrs,
        (∀ node,next.valid node ↔ graph.valid node ∨ node=heap) ∧ next.valid heap ∧
        next.Regions nodeLower (PersistentAlloc.rounded heap 56#64).toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
        next.PathBytes target.be ∧ next.PathRegions pathLower (PersistentAlloc.rounded heap 56#64).toNat ∧ next.PathSeparated := by
  obtain ⟨callee,called,nib,nlen,childCell⟩:=Input.word_triple_environment source.code.lookup (ofString "node_new_ext")
    (ofString "nib") (ofString "nlen") (ofString "child") (body .extension) .one key length child
    (by decide) (by decide) (by decide) (original_code .extension source.code installed)
  have inputs : Inputs .extension (callEntryStateHOLFinite source callee) (extensionWords key length child):=by
    simpa only [Inputs,extensionWords,callEntryStateHOLFinite,ite_true,ite_false,show ("nlen" : String)≠"nib" from by decide,
      show ("child" : String)≠"nib" from by decide,show ("child" : String)≠"nlen" from by decide] using And.intro nib (And.intro nlen childCell)
  obtain ⟨arena,endpoint⟩:=assigned_normal .extension (by decide) source target heap (extensionWords key length child) name arguments _ callee args called inputs
    domain heapCell frontier aligned installed normal
  have physical : Physical .extension source target heap (extensionWords key length child):=
    physical_of_fields .extension source target heap (extensionWords key length child) arena aligned
      (by rw [endpoint]; rfl) (by rw [endpoint]; rfl) (by rw [endpoint]; rfl) (by rw [endpoint]; rfl)
  have localsEq : target.locals=source.locals.update (name,.val (.word heap)):=by rw [endpoint]; rfl
  have codeEq : target.code=source.code:=by rw [endpoint]; rfl
  have clockEq : target.clock=source.clock-2:=by rw [endpoint]; rfl
  refine ⟨localsEq,codeEq,by rw [clockEq]; omega,physical,?_⟩
  exact physical.extension_path_graph source target heap (extensionWords key length child) domain aligned graph limit nodeLower pathLower property
    values regions disjoint paths pathRegions separated floor (by simpa [extensionWords] using buffer)
      (by simpa [extensionWords] using childMember) (by simpa [extensionWords] using positive)

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.extension_assigned_paths
