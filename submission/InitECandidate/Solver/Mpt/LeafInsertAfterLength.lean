import InitECandidate.Solver.Mpt.LeafInsertSplitNormal
import InitECandidate.Solver.Mpt.LeafInsertCompareNormal
import InitECandidate.Solver.Mpt.LeafInsertCost
import InitECandidate.Solver.Mpt.TrieProtectedMutation

namespace InitECandidate.Solver.Mpt.InsertLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Both real original249 outcomes after path loading: matching return or
comparison fallthrough followed by the genuine bounded split. -/
theorem after_length_path_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
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
    (small : length.toNat≤64) (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterLength=(some (.returned value),target)) :
    target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧ source.clock-target.clock≤5*length.toNat+242 ∧
      (∀ query : BitVec 64,query.toNat<nodeLower → target.memory query=source.memory query) ∧
      (∀ current,graph.valid current → current≠0#64 → wordAt target.memory current=wordAt source.memory current) ∧
      ∃ finalHeap root : BitVec 64,value=.val (.word root) ∧ target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ current,graph.valid current → next.valid current) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
          graph.PathFields target.memory ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat → target.memory address=source.memory address) ∧
          (∀ current,next.valid current → graph.valid current ∨ heap.toNat≤current.toNat) ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat →
            TrieWalk.PathWordAway key length.toNat address → next.ProtectedWord address) ∧ graph.CacheFrame target.memory ∧
          (TrieWalk.Uncached source.memory node→TrieWalk.Uncached target.memory root) := by
  have priced:=after_length_cost source (wordAt source.memory (node+32#64)) (wordAt source.memory (node+40#64)) key length small installed leftCell oldLengthCell keyCell lengthCell
  rw [normal] at priced
  rw [dispatch_shapes.2.2.1,evaluateHOLFiniteState_seq_line780] at normal
  generalize reached : evaluateHOLFiniteState source lengthChoice=output at normal
  obtain ⟨result,middle⟩:=output
  cases result with
  | none=>
    have frame:=length_choice_none_frame source middle (wordAt source.memory (node+32#64)) (wordAt source.memory (node+40#64)) key length installed leftCell oldLengthCell keyCell lengthCell reached
    have memoryEq:=congrArg PanSemStateFiniteExact.memory frame
    have domainEq:=congrArg PanSemStateFiniteExact.memaddrs frame
    have endianEq:=congrArg PanSemStateFiniteExact.be frame
    have codeEq:=congrArg PanSemStateFiniteExact.code frame
    have globalsEq:=congrArg PanSemStateFiniteExact.globals frame
    change middle.memory=source.memory at memoryEq
    change middle.memaddrs=source.memaddrs at domainEq
    change middle.be=source.be at endianEq
    change middle.code=source.code at codeEq
    change middle.globals=source.globals at globalsEq
    have current (name : MlS) (other : name≠ofString "eq") : middle.locals.lookup name=source.locals.lookup name:=by
      have summary:=(length_choice_flow name other).summary source
      unfold Input.FlowSummary at summary
      rw [reached] at summary
      exact summary.1 rfl
    obtain ⟨base,same,baseRegions,baseDisjoint,⟨baseValues⟩,basePaths,basePathRegions,baseSeparated⟩:=
      graph.after_erase source middle limit nodeLower heap.toNat pathLower heap.toNat property values regions disjoint paths pathRegions separated frame
    have currentQuery:=query.of_erase source middle graph base pathLower heap.toNat key length.toNat same frame
    have currentMember : base.valid node:=by rw [same]; exact member
    have currentLeaf : wordAt middle.memory node=1#64:=by rw [memoryEq]; exact leaf
    have currentLeft : middle.locals.lookup (ofString "ek")=some (.val (.word (wordAt middle.memory (node+32#64)))):=by rw [memoryEq,current _ (by decide)]; exact leftCell
    have currentLength : middle.locals.lookup (ofString "el")=some (.val (.word (wordAt middle.memory (node+40#64)))):=by rw [memoryEq,current _ (by decide)]; exact oldLengthCell
    obtain ⟨finalDomain,finalEndian,finalCode,finalPrice,finalMemory,finalHeap,root,answer,finalHeapCell,finalArena,finalAligned,grows,next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,finalFresh,finalProtection,rootClean⟩:=
      split_scope_path_normal middle target heap node key length pointer size base limit nodeLower pathLower property baseValues baseRegions baseDisjoint basePaths basePathRegions baseSeparated
        currentQuery currentMember active currentLeaf ((current _ (by decide)).trans nodeCell) currentLeft currentLength
        ((current _ (by decide)).trans keyCell) ((current _ (by decide)).trans lengthCell) ((current _ (by decide)).trans pointerCell) ((current _ (by decide)).trans sizeCell)
        (by rw [domainEq]; exact payload) extra floor empty (domainEq.trans domain) (by rw [globalsEq]; exact heapCell) frontier aligned (by rw [codeEq]; exact installed) small value normal
    have preserved (query : BitVec 64) (before : query.toNat<nodeLower) : target.memory query=source.memory query:=
      (finalMemory query (before.trans_le floor)).trans (congrFun memoryEq query)
    have tags (current : BitVec 64) (live : graph.valid current) (nonzero : current≠0#64) : wordAt target.memory current=wordAt source.memory current:=by
      have before : current.toNat<heap.toNat:=by
        have bounds:=(regions current live nonzero).2.2.2
        have size:=(TrieWalk.nodeBytes_bounds (wordAt source.memory current)).1
        omega
      unfold wordAt
      rw [finalMemory current before,memoryEq]
    have inclusion (current : BitVec 64) (live : graph.valid current) : next.valid current:=members current (by rw [same]; exact live)
    exact ⟨finalDomain.trans domainEq,finalEndian.trans endianEq,finalCode.trans codeEq,priced,preserved,tags,finalHeap,root,answer,finalHeapCell,finalArena,finalAligned,grows,
      next,inclusion,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,
      TrieWalk.Graph.PathFields.of_prefix graph target.memory nodeLower heap.toNat regions
        (fun address before=>(finalMemory address before).trans (congrFun memoryEq address)),
      (by intro address _safe before; exact (finalMemory address before).trans (congrFun memoryEq address)),
      (by
        intro current live
        rcases finalFresh current live with old|fresh
        · exact Or.inl (by rwa [same] at old)
        · exact Or.inr fresh),
      (by
        intro address safe before away
        have pureFields : graph.PathFields middle.memory:=by
          rw [memoryEq]
          exact ⟨by intro node live active; rfl,by intro node live active tag; exact ⟨rfl,rfl⟩⟩
        exact finalProtection address (safe.of_fields graph base address same pureFields) before away),
      graph.cache_of_older nodeLower heap.toNat regions (fun address before=>(finalMemory address before).trans (congrFun memoryEq address)),
      (fun _=>rootClean)⟩
  | some result=>
    have sameResult : result=.returned value:=Option.some.inj (congrArg Prod.fst normal)
    subst result
    have targetEq : target=middle:=(congrArg Prod.snd normal).symm
    subst target
    have compared:=length_choice_return source middle (wordAt source.memory (node+40#64)) length oldLengthCell lengthCell value reached
    obtain ⟨answer,frame,next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
      compare_scope_path_normal source middle node pointer size (wordAt source.memory (node+32#64)) (wordAt source.memory (node+40#64)) key graph limit nodeLower heap.toNat pathLower heap.toNat property
        values regions disjoint paths pathRegions separated member active leaf nodeCell pointerCell sizeCell leftCell oldLengthCell keyCell installed domain payload extra value compared
    have memoryEq:=congrArg PanSemStateFiniteExact.memory frame
    have domainEq:=congrArg PanSemStateFiniteExact.memaddrs frame
    have endianEq:=congrArg PanSemStateFiniteExact.be frame
    have codeEq:=congrArg PanSemStateFiniteExact.code frame
    have globalsEq:=congrArg PanSemStateFiniteExact.globals frame
    change middle.memory=(post source node pointer size).memory at memoryEq
    change middle.memaddrs=source.memaddrs at domainEq
    change middle.be=source.be at endianEq
    change middle.code=source.code at codeEq
    change middle.globals=source.globals at globalsEq
    have arena : AllocatedBytes.Arena node 64:=by simpa [leaf,TrieWalk.nodeBytes] using (regions node member active).2.1
    have nodeFloor : nodeLower≤node.toNat:=(regions node member active).1
    have preserved (query : BitVec 64) (before : query.toNat<nodeLower) : middle.memory query=source.memory query:=by
      rw [memoryEq]
      have away (offset : Nat) (inside : offset<64) : query≠byteAddress node offset:=by
        intro equal
        have number:=congrArg BitVec.toNat equal
        rw [byteAddress_toNat node offset (by have upper:=arena.upper; omega)] at number
        omega
      exact post_away source node pointer size query (away 48 (by decide)) (away 56 (by decide))
    have tags (current : BitVec 64) (live : graph.valid current) (nonzero : current≠0#64) : wordAt middle.memory current=wordAt source.memory current:=by
      have away:=graph.leaf_value_away nodeLower heap.toNat regions disjoint node current member active leaf (.header current live nonzero)
      unfold wordAt
      rw [memoryEq,post_away source node pointer size current away.1 away.2]
    have rootMember : next.valid node:=by rw [same]; exact member
    have inclusion (current : BitVec 64) (live : graph.valid current) : next.valid current:=by rw [same]; exact live
    have allFields : graph.PathFields middle.memory:=by
      have agree : ∀ address,graph.Footprint address→(post source node pointer size).memory address=source.memory address:=by
        intro address needed
        have apart:=graph.leaf_value_away nodeLower heap.toNat regions disjoint node address member active leaf needed
        exact post_away source node pointer size address apart.1 apart.2
      rw [memoryEq]
      exact TrieWalk.Graph.PathFields.of_agreement graph (post source node pointer size).memory agree
    refine ⟨domainEq,endianEq,codeEq,priced,preserved,tags,heap,node,answer,(by rw [globalsEq]; exact heapCell),frontier,aligned,Nat.le_refl _,
      next,inclusion,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,allFields,?_,?_,?_,?_,?_⟩
    · intro address safe _before
      rw [memoryEq]
      exact safe.leaf_value_memory source graph address node pointer size member active leaf
    · intro current live
      exact Or.inl (by rwa [same] at live)
    · intro address safe _before _away
      exact safe.of_fields graph next address same allFields
    · rw [memoryEq]
      exact graph.cache_leaf_update source nodeLower heap.toNat regions disjoint node pointer size member active leaf
    · have caches : graph.CacheFrame middle.memory:=by
        rw [memoryEq]
        exact graph.cache_leaf_update source nodeLower heap.toNat regions disjoint node pointer size member active leaf
      exact caches.uncached graph node member

end InitECandidate.Solver.Mpt.InsertLeaf

#print axioms InitECandidate.Solver.Mpt.InsertLeaf.after_length_path_normal
