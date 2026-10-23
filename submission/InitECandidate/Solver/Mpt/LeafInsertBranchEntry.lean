import InitECandidate.Solver.Mpt.LeafInsertSplitProgram
import InitECandidate.Solver.Mpt.TwoLeavesScoped
import InitECandidate.Solver.Mpt.TriePathBufferBounds

namespace InitECandidate.Solver.Mpt.InsertLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original leaf split calls248 with its actual stored value and
two real borrowed suffixes. Its genuine normal return supplies the fresh
branch and a protected old-path prefix for the optional extension. -/
theorem branch_entry_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key length pointer size prefixLength : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (member : graph.valid node) (active : node≠0#64) (leaf : wordAt source.memory node=1#64)
    (bound : prefixLength.toNat≤min (wordAt source.memory (node+40#64)).toNat length.toNat)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (leftCell : source.locals.lookup (ofString "ek")=some (.val (.word (wordAt source.memory (node+32#64)))))
    (oldLengthCell : source.locals.lookup (ofString "el")=some (.val (.word (wordAt source.memory (node+40#64)))))
    (keyCell : source.locals.lookup (ofString "rk")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "rl")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (prefixCell : source.locals.lookup (ofString "pl")=some (.val (.word prefixLength)))
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterPrefix=(some (.returned value),target)) :
    ∃ ready inner,ready.locals.lookup (ofString "br")=some (.val (.word heap)) ∧
      ready.locals=source.locals.update (ofString "br",.val (.word heap)) ∧ ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧ ready.code=source.code ∧
      source.clock-ready.clock≤236 ∧ evaluateHOLFiniteState ready afterBranch=(some (.returned value),inner) ∧ target=restore source "br" inner ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → ready.memory query=source.memory query) ∧
      ∃ finalHeap : BitVec 64,ready.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧ wordAt ready.memory heap=3#64 ∧
        ∃ next : TrieWalk.Graph ready.memory ready.memaddrs,
          (∀ current,graph.valid current → next.valid current) ∧ next.valid heap ∧ next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧
          Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes ready.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
          next.PathBuffer ready.be pathLower finalHeap.toNat (wordAt source.memory (node+32#64)) prefixLength.toNat ∧
          (∀ current,next.valid current → graph.valid current ∨ heap.toNat≤current.toNat) ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat →
            TrieWalk.PathWordAway key length.toNat address → next.ProtectedWord address) := by
  let oldValue:=values.leaf node member active leaf
  let oldBuffer:=TrieWalk.Graph.PathBuffer.stored graph source.be pathLower heap.toNat paths pathRegions separated node member active (Or.inl leaf)
  have leftBound : prefixLength.toNat≤(wordAt source.memory (node+40#64)).toNat:=bound.trans (Nat.min_le_left _ _)
  have rightBound : prefixLength.toNat≤length.toNat:=bound.trans (Nat.min_le_right _ _)
  have leftSub : (wordAt source.memory (node+40#64)-prefixLength).toNat=(wordAt source.memory (node+40#64)).toNat-prefixLength.toNat:=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact leftBound)
  have rightSub : (length-prefixLength).toNat=length.toNat-prefixLength.toNat:=BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact rightBound)
  have first:=oldBuffer.window graph source.be pathLower heap.toNat _ prefixLength _ (wordAt source.memory (node+40#64)-prefixLength).toNat leftBound (by rw [leftSub])
  have second:=query.window graph source.be pathLower heap.toNat key prefixLength length.toNat (length-prefixLength).toNat rightBound (by rw [rightSub])
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) branchArguments=
      some (TwoLeaves.values (wordAt source.memory (node+32#64)+prefixLength) (wordAt source.memory (node+40#64)-prefixLength) oldValue.pointer oldValue.length
        (key+prefixLength) (length-prefixLength) pointer size):=by
    simp [branchArguments,TwoLeaves.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,addConst,localVar,toExact,nodeCell,leftCell,oldLengthCell,keyCell,lengthCell,pointerCell,sizeCell,prefixCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,oldValue.pointerMapped,oldValue.pointerStored,oldValue.lengthMapped,oldValue.lengthStored]
  rw [split_shapes.1] at normal
  obtain ⟨ready,inner,branchCell,localsEq,domainEq,endianEq,codeEq,price,continued,endpoint,olderMemory,finalHeap,nextHeapCell,nextArena,nextAligned,grows,branchTag,next,oldMember,branchMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,firstAfter,secondAfter,provenance,protection⟩:=
    TwoLeaves.scoped_path_normal source target heap (wordAt source.memory (node+32#64)+prefixLength) (wordAt source.memory (node+40#64)-prefixLength) oldValue.pointer oldValue.length
      (key+prefixLength) (length-prefixLength) pointer size graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated first second
      oldValue.payload oldValue.extra payload extra floor empty domain heapCell frontier aligned installed value "br" branchArguments afterBranch args normal
  have nodeMemory:=olderMemory node (graph.footprint_bounds nodeLower heap.toNat regions node (.header node member active)).2
  have keyMemory:=olderMemory (node+32#64) (graph.footprint_bounds nodeLower heap.toNat regions _ (.pointer node member active (Or.inl leaf))).2
  have lengthMemory:=olderMemory (node+40#64) (graph.footprint_bounds nodeLower heap.toNat regions _ (.size node member active (Or.inl leaf))).2
  have currentLeaf : wordAt ready.memory node=1#64:=by unfold wordAt; rw [nodeMemory]; exact leaf
  have keyWord : wordAt ready.memory (node+32#64)=wordAt source.memory (node+32#64):=congrArg MemoryBytes.wordBits keyMemory
  have lengthWord : wordAt ready.memory (node+40#64)=wordAt source.memory (node+40#64):=congrArg MemoryBytes.wordBits lengthMemory
  have full:=TrieWalk.Graph.PathBuffer.stored next ready.be pathLower finalHeap.toNat nextPaths nextPathRegions nextSeparated node (oldMember node member) active (Or.inl currentLeaf)
  rw [keyWord,lengthWord] at full
  have leading:=full.window next ready.be pathLower finalHeap.toNat _ 0#64 _ prefixLength.toNat
    (by change 0≤(wordAt source.memory (node+40#64)).toNat; omega) (by change prefixLength.toNat≤(wordAt source.memory (node+40#64)).toNat; exact leftBound)
  have prefixBuffer : next.PathBuffer ready.be pathLower finalHeap.toNat (wordAt source.memory (node+32#64)) prefixLength.toNat:=by
    simpa only [BitVec.add_zero] using leading
  have finalProtection (address : BitVec 64) (safe : graph.ProtectedWord address) (before : address.toNat<heap.toNat)
      (away : TrieWalk.PathWordAway key length.toNat address) : next.ProtectedWord address:=by
    have oldAway:=safe.stored graph address node member active (Or.inl leaf)
    exact protection address safe before
      (oldAway.window _ prefixLength address _ _ leftBound (by rw [leftSub]))
      (away.window key prefixLength address length.toNat _ rightBound (by rw [rightSub]))
  exact ⟨ready,inner,branchCell,localsEq,domainEq,endianEq,codeEq,price,continued,endpoint,olderMemory,finalHeap,nextHeapCell,nextArena,nextAligned,grows,branchTag,
    next,oldMember,branchMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,prefixBuffer,provenance,finalProtection⟩

end InitECandidate.Solver.Mpt.InsertLeaf

#print axioms InitECandidate.Solver.Mpt.InsertLeaf.branch_entry_normal
