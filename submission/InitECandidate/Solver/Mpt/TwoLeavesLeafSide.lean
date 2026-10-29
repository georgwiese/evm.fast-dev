import InitECandidate.Solver.Mpt.TwoLeavesLeafEntry
import InitECandidate.Solver.Mpt.TwoLeavesChildStore
import InitECandidate.Solver.WitnessRadix.Bindings
import InitECandidate.Solver.Mpt.NodeConstructorProtected
import InitECandidate.Solver.Mpt.TrieCacheMutation

namespace InitECandidate.Solver.Mpt.TwoLeaves
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The whole original nonempty side, through its genuine fresh leaf,
nibble-selected child store and restored caller scope. -/
theorem leaf_side_paths (second : Bool) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap key length pointer size otherKey otherLength branch : BitVec 64)
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
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word branch)))
    (branchMember : graph.valid branch) (branchActive : branch≠0#64) (tag : wordAt source.memory branch=3#64)
    (normal : evaluateHOLFiniteState source (leafScope second)=(none,post)) :
    post.locals=source.locals ∧ post.memaddrs=source.memaddrs ∧ post.be=source.be ∧ post.code=source.code ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 64#64))) ∧
      AllocatedBytes.Arena (PersistentAlloc.rounded heap 64#64) 0 ∧ (PersistentAlloc.rounded heap 64#64).toNat%8=0 ∧
      heap.toNat≤(PersistentAlloc.rounded heap 64#64).toNat ∧ wordAt post.memory branch=3#64 ∧
      (∀ query : BitVec 64,query.toNat<branch.toNat → post.memory query=source.memory query) ∧
      ∃ next : TrieWalk.Graph post.memory post.memaddrs,
        (∀ node,next.valid node ↔ graph.valid node ∨ node=heap) ∧ next.valid branch ∧ next.valid heap ∧
        next.Regions nodeLower (PersistentAlloc.rounded heap 64#64).toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
        next.PathBytes post.be ∧ next.PathRegions pathLower (PersistentAlloc.rounded heap 64#64).toNat ∧ next.PathSeparated ∧
        next.PathBuffer post.be pathLower (PersistentAlloc.rounded heap 64#64).toNat key length.toNat ∧
        next.PathBuffer post.be pathLower (PersistentAlloc.rounded heap 64#64).toNat otherKey otherLength.toNat ∧
        (∀ query : BitVec 64,graph.ProtectedWord query → query.toNat<heap.toNat →
          TrieWalk.PathWordAway key length.toNat query → next.ProtectedWord query) ∧ graph.CacheFrame post.memory := by
  obtain ⟨ready,inner,leafCell,localsEq,physical,codeEq,continued,endpoint,base,members,member,baseRegions,baseDisjoint,⟨baseValues⟩,basePaths,basePathRegions,baseSeparated,first,other⟩:=
    leaf_entry second source post heap key length pointer size otherKey otherLength graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated
      buffer otherBuffer positive floor keyCell lengthCell pointerCell sizeCell payload extra domain heapCell frontier aligned installed normal
  have branchDifferent : ofString "br"≠ofString (label second "lf1" "lf2"):=by cases second <;> decide
  have keyDifferent : ofString (label second "k1" "k2")≠ofString (label second "lf1" "lf2"):=by cases second <;> decide
  have currentBranch : ready.locals.lookup (ofString "br")=some (.val (.word branch)):=by
    rw [localsEq]
    simpa [HolFiniteMapExact.update,FUPDATE,Ne.symm branchDifferent] using branchCell
  have currentKey : ready.locals.lookup (ofString (label second "k1" "k2"))=some (.val (.word key)):=by
    rw [localsEq]
    simpa [HolFiniteMapExact.update,FUPDATE,Ne.symm keyDifferent] using keyCell
  have oldBranchBounds:=regions branch branchMember branchActive
  have branchBefore : branch.toNat<heap.toNat:=by have size:=(TrieWalk.nodeBytes_bounds (wordAt source.memory branch)).1; omega
  have currentTag : wordAt ready.memory branch=3#64:=by
    unfold wordAt
    rw [physical.memory branch (Or.inl branchBefore)]
    exact tag
  have currentMember : base.valid branch:=(members branch).mpr (Or.inl branchMember)
  obtain ⟨index,small,stored,next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    leaf_store_paths second ready branch heap key length.toNat first.span positive currentBranch currentKey leafCell base limit nodeLower
      (PersistentAlloc.rounded heap 64#64).toNat pathLower (PersistentAlloc.rounded heap 64#64).toNat property baseValues baseRegions baseDisjoint basePaths basePathRegions baseSeparated
      currentMember branchActive currentTag member
  let changed:={ready with memory:=StoreWord.put ready.memory (branch+BitVec.ofNat 64 (32+index*8)) heap}
  have innerEq : inner=changed:=congrArg Prod.snd (continued.symm.trans stored)
  have notHash : wordAt ready.memory branch≠0#64:=by rw [currentTag]; decide
  have notLeaf : wordAt ready.memory branch≠1#64:=by rw [currentTag]; decide
  have notExtension : wordAt ready.memory branch≠2#64:=by rw [currentTag]; decide
  have slot : TrieWalk.ChildSlot ready.memory branch (32+index*8):=.branch notHash notLeaf notExtension index small
  have tags : ∀ node,base.valid node → node≠0#64 → wordAt changed.memory node=wordAt ready.memory node:=by
    intro node live active
    apply congrArg MemoryBytes.wordBits
    exact if_neg (base.child_store_header_away nodeLower (PersistentAlloc.rounded heap 64#64).toNat baseRegions baseDisjoint branch (32+index*8) slot currentMember branchActive node live active)
  have firstAfter:=first.after_child_store ready base pathLower (PersistentAlloc.rounded heap 64#64).toNat key length.toNat branch heap (32+index*8) slot currentMember branchActive next same tags
  have otherAfter:=other.after_child_store ready base pathLower (PersistentAlloc.rounded heap 64#64).toNat otherKey otherLength.toNat branch heap (32+index*8) slot currentMember branchActive next same tags
  have nextBranch : next.valid branch:=by rw [same]; exact currentMember
  have nextLeaf : next.valid heap:=by rw [same]; exact member
  have finalTag : wordAt changed.memory branch=3#64:=(tags branch currentMember branchActive).trans currentTag
  have finalMembers (node : BitVec 64) : next.valid node ↔ graph.valid node ∨ node=heap:=by rw [same]; exact members node
  have grows : heap.toNat≤(PersistentAlloc.rounded heap 64#64).toNat:=by
    have before : heap.toNat+64≤(PersistentAlloc.rounded heap 64#64).toNat:=physical.before
    omega
  have prefixMemory (query : BitVec 64) (before : query.toNat<branch.toNat) : changed.memory query=source.memory query:=by
    have arena:=(baseRegions branch currentMember branchActive).2.1
    have within : 32+index*8<TrieWalk.nodeBytes (wordAt ready.memory branch):=slot.bounds ready.memory branch (32+index*8) |>.2.2.1
    have away : query≠branch+BitVec.ofNat 64 (32+index*8):=by
      intro equal
      have number:=congrArg BitVec.toNat equal
      change query.toNat=(byteAddress branch (32+index*8)).toNat at number
      rw [byteAddress_toNat branch (32+index*8) (by have fits:=arena.upper; omega)] at number
      omega
    change StoreWord.put ready.memory (branch+BitVec.ofNat 64 (32+index*8)) heap query=source.memory query
    rw [StoreWord.put,if_neg away]
    exact physical.memory query (Or.inl (before.trans branchBefore))
  have protection (query : BitVec 64) (safe : graph.ProtectedWord query) (before : query.toNat<heap.toNat)
      (pathAway : TrieWalk.PathWordAway key length.toNat query) : next.ProtectedWord query:=by
    have subtraction : (length-1#64).toNat=length.toNat-1:=BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact positive)
    have suffixAway:=pathAway.window key 1#64 query length.toNat (length-1#64).toNat (by exact positive) (by rw [subtraction]; exact Nat.le_refl _)
    have baseSafe:=(physical.path_protected .leaf (Or.inl rfl) source ready heap _ graph base nodeLower regions members query safe before
      (by simpa [NodeConstructor.leafWords] using suffixAway)).2
    have storeFields:=TrieWalk.Graph.PathFields.of_child_store base nodeLower (PersistentAlloc.rounded heap 64#64).toNat baseRegions baseDisjoint
      branch heap (32+index*8) slot currentMember branchActive
    exact baseSafe.of_fields base next query same storeFields
  have caches : graph.CacheFrame changed.memory:=by
    intro node live active offset cache zero
    have retained:=(physical.cache_frame graph nodeLower regions) node live active offset cache zero
    exact (base.cache_child_store nodeLower (PersistentAlloc.rounded heap 64#64).toNat baseRegions baseDisjoint branch heap (32+index*8) slot currentMember branchActive)
      node ((members node).mpr (Or.inl live)) active offset cache retained
  rw [endpoint,innerEq]
  have restoredLocals : (restore source (label second "lf1" "lf2") changed).locals=source.locals:=by
    change HolFiniteMapExact.resVarEq ready.locals (ofString (label second "lf1" "lf2"),source.locals.lookup (ofString (label second "lf1" "lf2")))=source.locals
    rw [localsEq]
    exact congrArg PanSemStateFiniteExact.locals (restore_bound source (label second "lf1" "lf2") heap)
  exact ⟨restoredLocals,physical.domain,physical.endian,codeEq,physical.heapCell,physical.nextArena,physical.nextAligned,grows,finalTag,prefixMemory,
    next,finalMembers,nextBranch,nextLeaf,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,firstAfter,otherAfter,protection,caches⟩

end InitECandidate.Solver.Mpt.TwoLeaves

#print axioms InitECandidate.Solver.Mpt.TwoLeaves.leaf_side_paths
