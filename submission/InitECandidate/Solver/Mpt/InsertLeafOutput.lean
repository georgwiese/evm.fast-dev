import InitECandidate.Solver.Mpt.InsertDispatchProgram
import InitECandidate.Solver.Mpt.LeafInsertAssignedPaths
import InitECandidate.Solver.Mpt.InsertNodeOutputTerminal
import InitECandidate.Solver.Mpt.InsertPending

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real nonempty leaf case of original251 calls unchanged249 with
its actual remaining-key suffix and packages the terminal physical result. -/
theorem leaf_output_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key level length pointer size : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (pending : Pending source) (member : graph.valid node) (active : node≠0#64)
    (tag : wordAt source.memory node=1#64)
    (nodeClean : TrieWalk.Uncached source.memory node)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (before : level.toNat≤length.toNat) (bounded : length.toNat≤64)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (installed : Input.OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (normal : evaluateHOLFiniteState source insertLeafCall=(none,target)) :
    Nonempty (NodeOutput source target graph heap key length level limit nodeLower pathLower property) := by
  have subtraction : (length-level).toNat=length.toNat-level.toNat:=BitVec.toNat_sub_of_le (by rwa [BitVec.le_def])
  have suffix:=query.window graph source.be pathLower heap.toNat key level length.toNat (length-level).toNat before (by rw [subtraction])
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) insertLeafArguments=
      some (InsertLeaf.callValues node (key+level) (length-level) pointer size):=by
    simp [insertLeafArguments,queryPointer,queryLength,InsertLeaf.callValues,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,
      nodeCell,keyCell,levelCell,lengthCell,pointerCell,sizeCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [dispatch_shapes.2.2.2.2.2.2.1] at normal
  obtain ⟨root,localsEq,domainEq,endianEq,codeEq,price,memory,tags,finalHeap,finalHeapCell,finalArena,finalAligned,grows,next,members,rootMember,nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated,fields,protectedWords,provenance,protection,cacheFrame,rootClean,rootPositive,rootNonHash⟩:=
    InsertLeaf.assigned_path_normal source target heap node (key+level) (length-level) pointer size graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated
      suffix member active tag payload extra floor empty domain heapCell frontier aligned installed (by rw [subtraction]; omega) (ofString "r") insertLeafArguments args normal
  exact terminal_output source target heap key length level root finalHeap graph limit nodeLower pathLower property pending.node pending.slot pending.level pending.go localsEq
    domainEq endianEq codeEq finalHeapCell finalArena finalAligned grows memory fields protectedWords tags next members rootMember nextValues nextRegions nextDisjoint nextPaths nextPathRegions nextSeparated provenance
    (by
      intro address safe beforeHeap away
      exact protection address safe beforeHeap (away.window key level address length.toNat _ before (by rw [subtraction])))
    cacheFrame (rootClean nodeClean) rootPositive rootNonHash

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.leaf_output_normal
