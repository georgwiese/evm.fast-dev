import InitECandidate.Solver.Mpt.InsertDispatchProgram
import InitECandidate.Solver.Mpt.LeafAssignedPathGraph
import InitECandidate.Solver.Mpt.InsertNodeOutputTerminal
import InitECandidate.Solver.Mpt.InsertPending
import InitECandidate.Solver.Mpt.TriePathBufferOldPrefix
import InitECandidate.Solver.Mpt.NodeConstructorProtected

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- An actual null-child insertion creates its real leaf at any current
key level, retaining every older registered node, value and full path. -/
theorem empty_node_output (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap key level length pointer size : BitVec 64) (graph : TrieWalk.Graph source.memory source.memaddrs)
    (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (pending : Pending source)
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (before : level.toNat≤length.toNat) (_bounded : length.toNat≤64)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (floor : nodeLower≤heap.toNat) (_empty : property 0#64 0#64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (installed : Input.OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (normal : evaluateHOLFiniteState source leafCall=(none,target)) :
    Nonempty (NodeOutput source target graph heap key length level limit nodeLower pathLower property) := by
  have subtraction : (length-level).toNat=length.toNat-level.toNat:=BitVec.toNat_sub_of_le (by rwa [BitVec.le_def])
  have suffix:=query.window graph source.be pathLower heap.toNat key level length.toNat (length-level).toNat before (by rw [subtraction])
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) leafArguments=
      some [.val (.word (key+level)),.val (.word (length-level)),.val (.word pointer),.val (.word size)]:=by
    simp [leafArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,keyCell,levelCell,lengthCell,pointerCell,sizeCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [leafCall] at normal
  obtain ⟨localsEq,codeEq,price,physical,next,members,rootMember,nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated⟩:=
    NodeConstructor.leaf_assigned_paths source target heap (key+level) (length-level) pointer size (ofString "r") leafArguments graph limit nodeLower pathLower property
      values regions disjoint paths pathRegions separated suffix payload extra floor args domain heapCell frontier aligned installed normal
  have grows : heap.toNat≤(PersistentAlloc.rounded heap 64#64).toNat:=by have before : heap.toNat+64≤(PersistentAlloc.rounded heap 64#64).toNat:=physical.before; omega
  have memory (address : BitVec 64) (before : address.toNat<nodeLower) : target.memory address=source.memory address:=physical.memory address (Or.inl (before.trans_le floor))
  have tags (current : BitVec 64) (live : graph.valid current) (active : current≠0#64) : wordAt target.memory current=wordAt source.memory current:=by
    unfold wordAt
    rw [physical.memory current (Or.inl (regions.footprint_before graph nodeLower heap.toNat current (.header current live active)))]
  exact terminal_output source target heap key length level heap (PersistentAlloc.rounded heap 64#64) graph limit nodeLower pathLower property pending.node pending.slot pending.level pending.go localsEq
    physical.domain physical.endian codeEq physical.heapCell physical.nextArena physical.nextAligned grows memory
    (TrieWalk.Graph.PathFields.of_prefix graph target.memory nodeLower heap.toNat regions
      (fun address before=>physical.memory address (Or.inl before)))
    (by intro address _safe before; exact physical.memory address (Or.inl before)) tags
    next (fun current live=>(members current).mpr (Or.inl live)) rootMember nextValues nextRegions nextDisjoint nextPaths nextPathRegions nextSeparated
    (by
      intro node live
      rcases (members node).mp live with old|new
      · exact Or.inl old
      · exact Or.inr (by rw [new]))
    (by
      intro address safe beforeHeap away
      have suffixAway:=away.window key level address length.toNat (length-level).toNat before (by rw [subtraction])
      exact (physical.path_protected .leaf (Or.inl rfl) source target heap _ graph next nodeLower regions members address safe beforeHeap
        (by simpa [NodeConstructor.leafWords] using suffixAway)).2)
    (physical.cache_frame graph nodeLower regions) (physical.uncached (Or.inl rfl)) physical.nonzero

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.empty_node_output
