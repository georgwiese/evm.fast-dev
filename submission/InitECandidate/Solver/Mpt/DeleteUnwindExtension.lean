import InitECandidate.Solver.Mpt.DeleteUnwindProgram
import InitECandidate.Solver.Mpt.DeleteUnwindOutput
import InitECandidate.Solver.Mpt.DeleteExtensionAssigned

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual extension unwind uses the initialized saved segment and
length, and the current registered result. Its helper derives the next
registry and retains every older saved parent descriptor. -/
theorem unwind_extension_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (saved : DeleteFrame.Saved) (result heap : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (view : saved.View source) (owned : saved.Owned graph) (extensionKind : saved.kind=.extension)
    (resultMember : graph.valid result) (floor : 2701131776≤pathLower) (nodeFloor : nodeLower≤heap.toNat)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word saved.pointer)))
    (nodeCell : source.locals.lookup (ofString "fnode")=some (.val (.word saved.node)))
    (resultCell : source.locals.lookup (ofString "res")=some (.val (.word result)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source unwindChoice=(none,target)) :
    Nonempty (ChoiceOutput source target graph heap limit nodeLower pathLower property) := by
  have args:=extension_arguments source saved result view extensionKind domain topCell nodeCell resultCell
  obtain ⟨segmentBuffer,positive⟩:=owned.extension_buffer source saved graph pathLower heap.toNat extensionKind paths pathRegions separated
  obtain ⟨member,active,tag,_data⟩:=owned
  have actualTag : wordAt source.memory saved.node=2#64:=by simpa only [extensionKind,DeleteFrame.Kind.tag] using tag
  rw [unwind_dispatch source saved view domain topCell,extensionKind] at normal
  obtain ⟨root,localsEq,domainEq,endianEq,codeEq,_price,globalsEq,older,fields,finalHeap,finalCell,finalArena,finalAligned,grows,fresh,
    next,members,rootMember,nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated⟩:=
    DeleteExtension.assigned_path_normal source target heap saved.node result (saved.words "seg") (saved.words "sl") graph limit nodeLower pathLower property
      values regions disjoint paths pathRegions separated segmentBuffer floor nodeFloor positive member active actualTag resultMember heapCell frontier aligned little domain installed
      (ofString "res") extensionArguments args normal
  exact ⟨⟨root,finalHeap,localsEq,domainEq,endianEq,codeEq,globalsEq,older,fields,finalCell,finalArena,finalAligned,grows,fresh,
    next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩⟩

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.unwind_extension_normal
