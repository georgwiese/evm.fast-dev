import InitECandidate.Solver.Mpt.SplitExtensionStorePaths
import InitECandidate.Solver.Mpt.LeafConstructorScopedNone
import InitECandidate.Solver.Mpt.LeafConstructorPathGraph
import InitECandidate.Solver.Mpt.TriePathBufferMutation
import InitECandidate.Solver.Mpt.TriePathBufferBounds
import InitECandidate.Solver.Mpt.TwoLeavesSideOutput
import InitECandidate.Solver.WitnessRadix.Bindings
import InitECandidate.Solver.Mpt.NodeConstructorProtected

namespace InitECandidate.Solver.Mpt.SplitExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual new-side leaf scope borrows the query suffix, installs
its genuine fresh leaf using the saved nibble index and restores the caller. -/
theorem new_leaf_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap branch key prefixLength remaining pointer size otherKey otherLength : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat (key+prefixLength) remaining.toNat)
    (query : graph.PathBuffer source.be pathLower heap.toNat otherKey otherLength.toNat)
    (positive : 0<remaining.toNat) (index : Nat) (small : index<16) (floor : nodeLower≤heap.toNat)
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word branch)))
    (keyCell : source.locals.lookup (ofString "rk")=some (.val (.word key)))
    (prefixCell : source.locals.lookup (ofString "pl")=some (.val (.word prefixLength)))
    (remainingCell : source.locals.lookup (ofString "kal")=some (.val (.word remaining)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (indexCell : source.locals.lookup (ofString "idx")=some (.val (.word (BitVec.ofNat 64 index))))
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (branchMember : graph.valid branch) (branchActive : branch≠0#64) (tag : wordAt source.memory branch=3#64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source newLeafScope=(none,target)) :
    Nonempty (TwoLeaves.ProtectedSideOutput source target graph heap (key+prefixLength) remaining otherKey otherLength branch limit nodeLower pathLower property) := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) newLeafArguments=
      some [.val (.word (key+prefixLength+1#64)),.val (.word (remaining-1#64)),.val (.word pointer),.val (.word size)]:=by
    simp [newLeafArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,keyCell,prefixCell,remainingCell,pointerCell,sizeCell,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.add_assoc]
  rw [new_shapes.2.2.2.2.2.2.1] at normal
  obtain ⟨funded,ready,inner,leafCell,localsEq,physical,codeEq,continued,endpoint⟩:=NodeConstructor.leaf_scoped_none_physical source target heap (key+prefixLength+1#64) (remaining-1#64) pointer size
    "lf" newLeafArguments newLeafStore args domain heapCell frontier aligned installed normal
  have subtraction : (remaining-1#64).toNat=remaining.toNat-1:=BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 1≤remaining.toNat; exact positive)
  have suffix:=buffer.window graph source.be pathLower heap.toNat (key+prefixLength) 1#64 remaining.toNat (remaining-1#64).toNat (by change 1≤remaining.toNat; omega) (by rw [subtraction]; exact Nat.le_refl _)
  obtain ⟨base,members,member,baseRegions,baseDisjoint,⟨baseValues⟩,basePaths,basePathRegions,baseSeparated⟩:=
    physical.leaf_path_graph source ready heap (NodeConstructor.leafWords (key+prefixLength+1#64) (remaining-1#64) pointer size) domain aligned graph limit nodeLower pathLower property
      values regions disjoint paths pathRegions separated floor (by simpa [NodeConstructor.leafWords] using suffix)
      (by simpa [NodeConstructor.leafWords] using payload) (by simpa [NodeConstructor.leafWords] using extra)
  have tagCell : ready.memory heap=.word 1#64:=by simpa [FieldStores.Value.word] using physical.cells ⟨0,.literal 1#64⟩ (by simp [NodeConstructor.fields])
  have actualTag : wordAt ready.memory heap=1#64:=by simp [wordAt,tagCell,MemoryBytes.wordBits]
  have arena : AllocatedBytes.Arena heap (TrieWalk.nodeBytes (wordAt ready.memory heap)):=by simpa [actualTag,TrieWalk.nodeBytes,NodeConstructor.bytes] using physical.arena
  have grows : heap.toNat≤(PersistentAlloc.rounded heap 64#64).toNat:=by have before : heap.toNat+64≤(PersistentAlloc.rounded heap 64#64).toNat:=physical.before; omega
  have olderMemory : ∀ query : BitVec 64,query.toNat<heap.toNat → ready.memory query=source.memory query:=fun query before=>physical.memory query (Or.inl before)
  have firstOld:=buffer.after_fresh_node source ready graph base nodeLower pathLower heap (key+prefixLength) remaining.toNat regions
    (fun node live=>(members node).mp live) arena physical.domain physical.endian olderMemory
  have queryOld:=query.after_fresh_node source ready graph base nodeLower pathLower heap otherKey otherLength.toNat regions
    (fun node live=>(members node).mp live) arena physical.domain physical.endian olderMemory
  have first:=firstOld.weaken base ready.be pathLower heap.toNat pathLower (PersistentAlloc.rounded heap 64#64).toNat _ _ (Nat.le_refl _) grows
  have currentQuery:=queryOld.weaken base ready.be pathLower heap.toNat pathLower (PersistentAlloc.rounded heap 64#64).toNat _ _ (Nat.le_refl _) grows
  have current (name : MlS) (other : name≠ofString "lf") : ready.locals.lookup name=source.locals.lookup name:=by rw [localsEq]; simp [HolFiniteMapExact.update,FUPDATE,Ne.symm other]
  have branchBefore : branch.toNat<heap.toNat:=by
    have bounds:=(regions branch branchMember branchActive).2.2.2
    have size:=(TrieWalk.nodeBytes_bounds (wordAt source.memory branch)).1
    omega
  have currentTag : wordAt ready.memory branch=3#64:=by unfold wordAt; rw [olderMemory branch branchBefore]; exact tag
  have currentMember : base.valid branch:=(members branch).mpr (Or.inl branchMember)
  obtain ⟨stored,tags,next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    new_store_paths ready branch heap index small
      ((current _ (by decide)).trans branchCell) ((current _ (by decide)).trans indexCell) leafCell
      base limit nodeLower (PersistentAlloc.rounded heap 64#64).toNat pathLower (PersistentAlloc.rounded heap 64#64).toNat property baseValues baseRegions baseDisjoint basePaths basePathRegions baseSeparated currentMember branchActive currentTag member
  let changed:={ready with memory:=StoreWord.put ready.memory (branch+BitVec.ofNat 64 (32+index*8)) heap}
  have innerEq : inner=changed:=congrArg Prod.snd (continued.symm.trans stored)
  have notHash : wordAt ready.memory branch≠0#64:=by rw [currentTag]; decide
  have notLeaf : wordAt ready.memory branch≠1#64:=by rw [currentTag]; decide
  have notExtension : wordAt ready.memory branch≠2#64:=by rw [currentTag]; decide
  have slot : TrieWalk.ChildSlot ready.memory branch (32+index*8):=.branch notHash notLeaf notExtension index small
  have firstAfter:=first.after_child_store ready base pathLower (PersistentAlloc.rounded heap 64#64).toNat (key+prefixLength) remaining.toNat branch heap (32+index*8) slot currentMember branchActive next same tags
  have queryAfter:=currentQuery.after_child_store ready base pathLower (PersistentAlloc.rounded heap 64#64).toNat otherKey otherLength.toNat branch heap (32+index*8) slot currentMember branchActive next same tags
  have prefixMemory (query : BitVec 64) (before : query.toNat<branch.toNat) : changed.memory query=source.memory query:=by
    have branchArena:=(baseRegions branch currentMember branchActive).2.1
    have within:=(slot.bounds ready.memory branch (32+index*8)).2.2.1
    have away : query≠branch+BitVec.ofNat 64 (32+index*8):=by
      intro equal
      have number:=congrArg BitVec.toNat equal
      change query.toNat=(byteAddress branch (32+index*8)).toNat at number
      rw [byteAddress_toNat branch (32+index*8) (by have upper:=branchArena.upper; omega)] at number
      omega
    change StoreWord.put ready.memory (branch+BitVec.ofNat 64 (32+index*8)) heap query=source.memory query
    rw [StoreWord.put,if_neg away]
    exact olderMemory query (before.trans branchBefore)
  have finalMembers (node : BitVec 64) (live : graph.valid node) : next.valid node:=by rw [same]; exact (members node).mpr (Or.inl live)
  have finalBranch : next.valid branch:=by rw [same]; exact currentMember
  have finalTag : wordAt changed.memory branch=3#64:=(tags branch currentMember branchActive).trans currentTag
  rw [endpoint,innerEq]
  have restoredLocals : (restore source "lf" changed).locals=source.locals:=by
    change HolFiniteMapExact.resVarEq ready.locals (ofString "lf",source.locals.lookup (ofString "lf"))=source.locals
    rw [localsEq]
    exact congrArg PanSemStateFiniteExact.locals (restore_bound source "lf" heap)
  exact ⟨{
    heap:=PersistentAlloc.rounded heap 64#64
    locals:=restoredLocals
    domain:=physical.domain
    endian:=physical.endian
    code:=codeEq
    heapCell:=physical.heapCell
    heapArena:=physical.nextArena
    heapAligned:=physical.nextAligned
    heapGrows:=grows
    branchTag:=finalTag
    olderPrefix:=prefixMemory
    cacheFrame:=by
      intro node live active offset cache zero
      have retained:=(physical.cache_frame graph nodeLower regions) node live active offset cache zero
      exact (base.cache_child_store nodeLower (PersistentAlloc.rounded heap 64#64).toNat baseRegions baseDisjoint branch heap (32+index*8) slot currentMember branchActive)
        node ((members node).mpr (Or.inl live)) active offset cache retained
    graph:=next
    oldMember:=finalMembers
    freshMembers:=by
      intro node live
      rw [same] at live
      rcases (members node).mp live with old|new
      · exact Or.inl old
      · exact Or.inr (by rw [new])
    protectedGraph:=by
      intro address safe before away
      have suffixAway:=away.window (key+prefixLength) 1#64 address remaining.toNat (remaining-1#64).toNat
        (by change 1≤remaining.toNat; omega) (by rw [subtraction]; exact Nat.le_refl _)
      have baseSafe:=(physical.path_protected .leaf (Or.inl rfl) source ready heap _ graph base nodeLower regions members address safe before
        (by simpa [NodeConstructor.leafWords] using suffixAway)).2
      have storeFields:=TrieWalk.Graph.PathFields.of_child_store base nodeLower (PersistentAlloc.rounded heap 64#64).toNat baseRegions baseDisjoint
        branch heap (32+index*8) slot currentMember branchActive
      exact baseSafe.of_fields base next address same storeFields
    branchMember:=finalBranch
    values:=Classical.choice nextValues
    regions:=nextRegions
    disjoint:=nextDisjoint
    paths:=nextPaths
    pathRegions:=nextPathRegions
    separated:=nextSeparated
    buffer:=firstAfter
    otherBuffer:=queryAfter }⟩

end InitECandidate.Solver.Mpt.SplitExtension

#print axioms InitECandidate.Solver.Mpt.SplitExtension.new_leaf_normal
