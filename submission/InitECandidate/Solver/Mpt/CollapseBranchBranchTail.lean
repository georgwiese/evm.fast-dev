import InitECandidate.Solver.Mpt.CollapseBranchSuffixProgram
import InitECandidate.Solver.Mpt.ExtensionConstructorTail
import InitECandidate.Solver.Mpt.ExtensionConstructorPathGraph
import InitECandidate.Solver.Input.SequenceChoice
import InitECandidate.Solver.Input.TailCallNoFallthrough

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem branch_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (tag : BitVec 64)
    (tagCell : source.locals.lookup (ofString "ck")=some (.val (.word tag))) :
    evaluateHOLFiniteState source afterStore=if tag=3#64 then evaluateHOLFiniteState source (.call none (ofString "node_new_ext") branchArguments)
      else evaluateHOLFiniteState source concatScope := by
  have guard : evaluateHOLFiniteState source branchGuard=if tag=3#64 then evaluateHOLFiniteState source (.call none (ofString "node_new_ext") branchArguments) else (none,source):=by
    rw [merge_shapes.2.1,evaluateHOLFiniteState_ite]
    by_cases selected : tag=3#64 <;> simp [evalHOLExact,toExact,localVar,tagCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,selected,evaluateHOLFiniteState_skip]
  rw [merge_shapes.1]
  exact Input.sequence_choice source branchGuard (.call none (ofString "node_new_ext") branchArguments) concatScope (tag=3#64) guard (.tail_call _ _)

/-- Original branch-child collapse constructs a positive one-nibble
extension over the genuinely registered child and the actual fresh byte.
The real tail call derives its own allocation and returned registry. -/
theorem branch_tail_paths (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nibble child : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat nibble 1) (floor : nodeLower≤heap.toNat) (childMember : graph.valid child)
    (nibbleCell : source.locals.lookup (ofString "nib")=some (.val (.word nibble)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (tagCell : source.locals.lookup (ofString "ck")=some (.val (.word 3#64)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (domain : source.memaddrs=InitE.ordinaryDomain)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterStore=(some (.returned value),target)) :
    value=.val (.word heap) ∧ source.clock-target.clock≤3 ∧ target.code=source.code ∧
      NodeConstructor.Physical .extension source target heap (NodeConstructor.extensionWords nibble 1#64 child) ∧
      ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ node,next.valid node ↔ graph.valid node ∨ node=heap) ∧ next.valid heap ∧
        next.Regions nodeLower (PersistentAlloc.rounded heap 56#64).toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
        next.PathBytes target.be ∧ next.PathRegions pathLower (PersistentAlloc.rounded heap 56#64).toNat ∧ next.PathSeparated := by
  rw [branch_dispatch source 3#64 tagCell,if_pos rfl] at normal
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) branchArguments=
      some [.val (.word nibble),.val (.word 1#64),.val (.word child)]:=by
    simp [branchArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,nibbleCell,childCell]
  obtain ⟨answer,physical,code,price⟩:=NodeConstructor.extension_tail_physical source target heap nibble 1#64 child branchArguments args domain heapCell frontier aligned installed value normal
  have registered:=physical.extension_path_graph source target heap (NodeConstructor.extensionWords nibble 1#64 child) domain aligned graph limit nodeLower pathLower property
    values regions disjoint paths pathRegions separated floor (by simpa [NodeConstructor.extensionWords] using buffer)
      (by simpa [NodeConstructor.extensionWords] using childMember) (by simp [NodeConstructor.extensionWords])
  exact ⟨answer,price,code,physical,registered⟩

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.branch_dispatch
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.branch_tail_paths
