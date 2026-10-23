import InitECandidate.Solver.Mpt.TwoLeavesProgram
import InitECandidate.Solver.Mpt.LeafConstructorScopedNone
import InitECandidate.Solver.Mpt.LeafConstructorPathGraph
import InitECandidate.Solver.Mpt.TriePathBufferMutation
import InitECandidate.Solver.Mpt.TriePathBufferBounds

namespace InitECandidate.Solver.Mpt.TwoLeaves
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem nonzero_choice (second : Bool) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64) (nonzero : length≠0#64)
    (lengthCell : source.locals.lookup (ofString (label second "l1" "l2"))=some (.val (.word length))) :
    evaluateHOLFiniteState source (choice second)=evaluateHOLFiniteState source (leafScope second) := by
  have read : eval source (.cmp .equal (localVar (label second "l1" "l2")) (.const 0#64))=some (.val (.word 0#64)):=by
    simp [eval,localVar,evalHOLExact,toExact,lengthCell,nonzero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [(side_shapes second).1,evaluateHOLFiniteState_ite]
  simp only [eval] at read
  rw [read]
  simp

/-- An actual nonzero side allocates a leaf borrowing the true suffix.
Both full independent buffers survive at its real child-store entry. -/
theorem leaf_entry (second : Bool) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap key length pointer size otherKey otherLength : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (otherBuffer : graph.PathBuffer source.be pathLower heap.toNat otherKey otherLength.toNat)
    (positive : 0<length.toNat) (floor : nodeLower≤heap.toNat)
    (keyCell : source.locals.lookup (ofString (label second "k1" "k2"))=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString (label second "l1" "l2"))=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString (label second "v1" "v2"))=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString (label second "vl1" "vl2"))=some (.val (.word size)))
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (leafScope second)=(none,post)) :
    ∃ ready inner,ready.locals.lookup (ofString (label second "lf1" "lf2"))=some (.val (.word heap)) ∧
      ready.locals=source.locals.update (ofString (label second "lf1" "lf2"),.val (.word heap)) ∧
      NodeConstructor.Physical .leaf source ready heap (NodeConstructor.leafWords (key+1#64) (length-1#64) pointer size) ∧ ready.code=source.code ∧
      evaluateHOLFiniteState ready (leafStore second)=(none,inner) ∧ post=restore source (label second "lf1" "lf2") inner ∧
      ∃ next : TrieWalk.Graph ready.memory ready.memaddrs,
        (∀ node,next.valid node ↔ graph.valid node ∨ node=heap) ∧ next.valid heap ∧
        next.Regions nodeLower (PersistentAlloc.rounded heap 64#64).toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
        next.PathBytes ready.be ∧ next.PathRegions pathLower (PersistentAlloc.rounded heap 64#64).toNat ∧ next.PathSeparated ∧
        next.PathBuffer ready.be pathLower (PersistentAlloc.rounded heap 64#64).toNat key length.toNat ∧
        next.PathBuffer ready.be pathLower (PersistentAlloc.rounded heap 64#64).toNat otherKey otherLength.toNat := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) (leafArguments second)=
      some [.val (.word (key+1#64)),.val (.word (length-1#64)),.val (.word pointer),.val (.word size)]:=by
    simp [leafArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,addConst,localVar,toExact,keyCell,lengthCell,pointerCell,sizeCell,
      valueIsWord,valueWord,wordOpHOL,wordOp]
  have called : evaluateHOLFiniteState source (.decCall (ofString (label second "lf1" "lf2")) .one (ofString "node_new_leaf") (leafArguments second) (leafStore second))=(none,post):=by
    rw [←(side_shapes second).2.1]
    exact normal
  obtain ⟨funded,ready,inner,leafCell,localsEq,physical,codeEq,continued,endpoint⟩:=NodeConstructor.leaf_scoped_none_physical source post heap (key+1#64) (length-1#64) pointer size
    (label second "lf1" "lf2") (leafArguments second) (leafStore second) args domain heapCell frontier aligned installed called
  have subtraction : (length-1#64).toNat=length.toNat-1:=BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact positive)
  have suffix:=buffer.window graph source.be pathLower heap.toNat key 1#64 length.toNat (length-1#64).toNat (by exact positive) (by rw [subtraction]; exact Nat.le_refl _)
  obtain ⟨next,members,member,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    physical.leaf_path_graph source ready heap (NodeConstructor.leafWords (key+1#64) (length-1#64) pointer size) domain aligned graph limit nodeLower pathLower property
      values regions disjoint paths pathRegions separated floor
      (by simpa [NodeConstructor.leafWords] using suffix) (by simpa [NodeConstructor.leafWords] using payload) (by simpa [NodeConstructor.leafWords] using extra)
  have tagCell : ready.memory heap=.word 1#64:=by
    simpa [FieldStores.Value.word] using physical.cells ⟨0,.literal 1#64⟩ (by simp [NodeConstructor.fields])
  have actualTag : wordAt ready.memory heap=1#64:=by simp [wordAt,tagCell,MemoryBytes.wordBits]
  have arena : AllocatedBytes.Arena heap (TrieWalk.nodeBytes (wordAt ready.memory heap)):=by
    simpa [actualTag,TrieWalk.nodeBytes,NodeConstructor.bytes] using physical.arena
  have grows : heap.toNat≤(PersistentAlloc.rounded heap 64#64).toNat:=by
    have before : heap.toNat+64≤(PersistentAlloc.rounded heap 64#64).toNat:=physical.before
    omega
  have memory : ∀ query : BitVec 64,query.toNat<heap.toNat → ready.memory query=source.memory query:=fun query before=>physical.memory query (Or.inl before)
  have first:=buffer.after_fresh_node source ready graph next nodeLower pathLower heap key length.toNat regions
    (fun node live=>(members node).mp live) arena physical.domain physical.endian memory
  have other:=otherBuffer.after_fresh_node source ready graph next nodeLower pathLower heap otherKey otherLength.toNat regions
    (fun node live=>(members node).mp live) arena physical.domain physical.endian memory
  exact ⟨ready,inner,leafCell,localsEq,physical,codeEq,continued,endpoint,next,members,member,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,
    first.weaken next ready.be pathLower heap.toNat pathLower (PersistentAlloc.rounded heap 64#64).toNat key length.toNat (Nat.le_refl _) grows,
    other.weaken next ready.be pathLower heap.toNat pathLower (PersistentAlloc.rounded heap 64#64).toNat otherKey otherLength.toNat (Nat.le_refl _) grows⟩

end InitECandidate.Solver.Mpt.TwoLeaves

#print axioms InitECandidate.Solver.Mpt.TwoLeaves.nonzero_choice
#print axioms InitECandidate.Solver.Mpt.TwoLeaves.leaf_entry
