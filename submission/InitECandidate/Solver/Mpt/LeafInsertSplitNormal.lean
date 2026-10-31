import InitECandidate.Solver.Mpt.LeafInsertAfterPrefix
import InitECandidate.Solver.Mpt.LeafInsertPrefixEntry
import InitECandidate.Solver.Mpt.TrieGraphPathErase

namespace InitECandidate.Solver.Mpt.InsertLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole original249 splitting scope: genuine bounded comparison,
actual branch creation and optional positive extension, retaining all old
registered data and every memory word below its incoming heap. -/
theorem split_scope_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key length pointer size : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (member : graph.valid node) (active : node≠0#64) (leaf : wordAt source.memory node=1#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (leftCell : source.locals.lookup (ofString "ek")=some (.val (.word (wordAt source.memory (node+32#64)))))
    (oldLengthCell : source.locals.lookup (ofString "el")=some (.val (.word (wordAt source.memory (node+40#64)))))
    (keyCell : source.locals.lookup (ofString "rk")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "rl")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (small : length.toNat≤64) (value : ValueHOL 64) (normal : evaluateHOLFiniteState source splitScope=(some (.returned value),target)) :
    target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧ source.clock-target.clock≤length.toNat+241 ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) ∧
      ∃ finalHeap root : BitVec 64,value=.val (.word root) ∧ target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ current,graph.valid current → next.valid current) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
          (∀ current,next.valid current → graph.valid current ∨ heap.toNat≤current.toNat) ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat →
            TrieWalk.PathWordAway key length.toNat address → next.ProtectedWord address) ∧ TrieWalk.Uncached target.memory root ∧ root≠0#64 ∧ wordAt target.memory root≠0#64 := by
  obtain ⟨ready,inner,prefixLength,bound,prefixCell,localsEq,frame,price,continued,endpoint⟩:=prefix_entry_normal source target (wordAt source.memory (node+32#64))
    (wordAt source.memory (node+40#64)) key length small installed leftCell oldLengthCell keyCell lengthCell value normal
  have memoryEq:=congrArg PanSemStateFiniteExact.memory frame
  have domainEq:=congrArg PanSemStateFiniteExact.memaddrs frame
  have endianEq:=congrArg PanSemStateFiniteExact.be frame
  have codeEq:=congrArg PanSemStateFiniteExact.code frame
  have globalsEq:=congrArg PanSemStateFiniteExact.globals frame
  change ready.memory=source.memory at memoryEq
  change ready.memaddrs=source.memaddrs at domainEq
  change ready.be=source.be at endianEq
  change ready.code=source.code at codeEq
  change ready.globals=source.globals at globalsEq
  obtain ⟨base,same,baseRegions,baseDisjoint,⟨baseValues⟩,basePaths,basePathRegions,baseSeparated⟩:=
    graph.after_erase source ready limit nodeLower heap.toNat pathLower heap.toNat property values regions disjoint paths pathRegions separated frame
  have currentQuery:=query.of_erase source ready graph base pathLower heap.toNat key length.toNat same frame
  have current (name : MlS) (other : name≠ofString "pl") : ready.locals.lookup name=source.locals.lookup name:=by
    rw [localsEq]
    simp [HolFiniteMapExact.update,FUPDATE,Ne.symm other]
  have currentMember : base.valid node:=by rw [same]; exact member
  have currentLeaf : wordAt ready.memory node=1#64:=by rw [memoryEq]; exact leaf
  have currentLeft : ready.locals.lookup (ofString "ek")=some (.val (.word (wordAt ready.memory (node+32#64)))):=by
    rw [memoryEq,current _ (by decide)]
    exact leftCell
  have currentLength : ready.locals.lookup (ofString "el")=some (.val (.word (wordAt ready.memory (node+40#64)))):=by
    rw [memoryEq,current _ (by decide)]
    exact oldLengthCell
  have readyBound : prefixLength.toNat≤min (wordAt ready.memory (node+40#64)).toNat length.toNat:=by rw [memoryEq]; exact bound
  obtain ⟨finalDomain,finalEndian,finalCode,finalPrice,finalMemory,finalHeap,root,answer,finalHeapCell,finalArena,finalAligned,grows,next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,finalFresh,finalProtection,rootClean,rootPositive,rootNonHash⟩:=
    after_prefix_path_normal ready inner heap node key length pointer size prefixLength base limit nodeLower pathLower property baseValues baseRegions baseDisjoint basePaths basePathRegions baseSeparated
      currentQuery currentMember active currentLeaf readyBound ((current _ (by decide)).trans nodeCell) currentLeft currentLength
      ((current _ (by decide)).trans keyCell) ((current _ (by decide)).trans lengthCell) ((current _ (by decide)).trans pointerCell) ((current _ (by decide)).trans sizeCell) prefixCell
      (by rw [domainEq]; exact payload) extra floor empty (domainEq.trans domain) (by rw [globalsEq]; exact heapCell) frontier aligned (by rw [codeEq]; exact installed) value continued
  have spent : source.clock-inner.clock≤length.toNat+241:=by omega
  have preserved (query : BitVec 64) (before : query.toNat<heap.toNat) : inner.memory query=source.memory query:=(finalMemory query before).trans (congrFun memoryEq query)
  have inclusion (current : BitVec 64) (live : graph.valid current) : next.valid current:=members current (by rw [same]; exact live)
  have provenance (current : BitVec 64) (live : next.valid current) : graph.valid current ∨ heap.toNat≤current.toNat:=by
    rcases finalFresh current live with old|fresh
    · exact Or.inl (by rwa [same] at old)
    · exact Or.inr fresh
  have protection (address : BitVec 64) (safe : graph.ProtectedWord address) (before : address.toNat<heap.toNat)
      (away : TrieWalk.PathWordAway key length.toNat address) : next.ProtectedWord address:=by
    have pureFields : graph.PathFields ready.memory:=by
      rw [memoryEq]
      exact ⟨by intro node live active; rfl,by intro node live active tag; exact ⟨rfl,rfl⟩⟩
    exact finalProtection address (safe.of_fields graph base address same pureFields) before away
  rw [endpoint]
  exact ⟨finalDomain.trans domainEq,finalEndian.trans endianEq,finalCode.trans codeEq,spent,preserved,finalHeap,root,answer,finalHeapCell,finalArena,finalAligned,grows,
    next,inclusion,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,provenance,protection,rootClean,rootPositive,rootNonHash⟩

end InitECandidate.Solver.Mpt.InsertLeaf

#print axioms InitECandidate.Solver.Mpt.InsertLeaf.split_scope_path_normal
