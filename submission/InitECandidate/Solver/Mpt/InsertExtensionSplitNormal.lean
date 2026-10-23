import InitECandidate.Solver.Mpt.InsertExtensionResultNormal
import InitECandidate.Solver.Mpt.SplitExtensionScopedPaths
import InitECandidate.Solver.Mpt.TriePathBufferOldPrefix
import InitECandidate.Solver.WitnessRadix.Bindings

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual original251 split scope calls unchanged250 and optionally
wraps its genuine branch in a positive extension. The old node itself
protects the full borrowed prefix after fresh branch/child registration. -/
theorem extension_split_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap node key level length prefixLength pointer size : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (query : graph.PathBuffer source.be pathLower heap.toNat key length.toNat)
    (member : graph.valid node) (active : node≠0#64) (tag : wordAt source.memory node=2#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word level)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (prefixCell : source.locals.lookup (ofString "pl")=some (.val (.word prefixLength)))
    (segmentCell : source.locals.lookup (ofString "seg")=some (.val (.word (wordAt source.memory (node+32#64)))))
    (before : level.toNat≤length.toNat) (strict : prefixLength.toNat<(wordAt source.memory (node+40#64)).toNat)
    (queryBound : prefixLength.toNat≤length.toNat-level.toNat)
    (payload : TrieWalk.Payload source.memaddrs pointer size limit) (extra : property pointer size)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source extensionSplitScope=(none,target)) :
    ∃ root : BitVec 64,target.locals=source.locals.update (ofString "r",.val (.word root)) ∧
      target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧ source.clock-target.clock≤239 ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) ∧
      (∀ current,graph.valid current → current≠0#64 → wordAt target.memory current=wordAt source.memory current) ∧
      ∃ finalHeap : BitVec 64,target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤finalHeap.toNat ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ current,graph.valid current → next.valid current) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated := by
  have subtraction : (length-level).toNat=length.toNat-level.toNat:=BitVec.toNat_sub_of_le (by rwa [BitVec.le_def])
  have suffix:=query.window graph source.be pathLower heap.toNat key level length.toNat (length-level).toNat before (by rw [subtraction])
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) splitArguments=
      some (SplitExtension.callValues node (key+level) (length-level) pointer size prefixLength):=by
    simp [splitArguments,insertLeafArguments,queryPointer,queryLength,SplitExtension.callValues,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,
      nodeCell,keyCell,levelCell,lengthCell,pointerCell,sizeCell,prefixCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  rw [extension_shapes.2.2.2.2.1] at normal
  obtain ⟨ready,inner,localsEq,domainEq,endianEq,codeEq,price,continued,endpoint,memory,currentHeap,currentHeapCell,currentArena,currentAligned,grows,branchTag,base,members,branchMember,baseRegions,baseDisjoint,⟨baseValues⟩,basePaths,basePathRegions,baseSeparated⟩:=
    SplitExtension.scoped_none_paths source target heap node (key+level) (length-level) prefixLength pointer size graph limit nodeLower pathLower property
      values regions disjoint paths pathRegions separated suffix member active tag strict (by rwa [subtraction]) payload extra floor empty domain heapCell frontier aligned installed
      "br" splitArguments extensionSplitChoice args normal
  have buffer:=TrieWalk.Graph.PathBuffer.old_stored_prefix source ready graph base nodeLower heap.toNat pathLower currentHeap.toNat regions basePaths basePathRegions baseSeparated
    node prefixLength member active (Or.inr tag) (members node member) (by omega) memory
  have current (name : MlS) (other : name≠ofString "br") : ready.locals.lookup name=source.locals.lookup name:=by
    rw [localsEq]
    simp [HolFiniteMapExact.update,FUPDATE,Ne.symm other]
  have currentBranch : ready.locals.lookup (ofString "br")=some (.val (.word heap)):=by rw [localsEq]; simp [HolFiniteMapExact.update,FUPDATE]
  obtain ⟨root,resultLocals,finalDomain,finalEndian,finalCode,finalPrice,finalMemory,finalTags,finalHeap,finalHeapCell,finalArena,finalAligned,finalGrows,next,finalMembers,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    extension_result_normal ready inner currentHeap (wordAt source.memory (node+32#64)) prefixLength heap base limit nodeLower pathLower property
      baseValues baseRegions baseDisjoint basePaths basePathRegions baseSeparated buffer branchMember (floor.trans grows)
      ((current _ (by decide)).trans segmentCell) ((current _ (by decide)).trans prefixCell) currentBranch
      (domainEq.trans domain) currentHeapCell currentArena currentAligned (by rw [codeEq]; exact installed) continued
  have olderMemory (query : BitVec 64) (before : query.toNat<heap.toNat) : inner.memory query=source.memory query:=
    (finalMemory query (before.trans_le grows)).trans (memory query before)
  have tags (current : BitVec 64) (live : graph.valid current) (nonzero : current≠0#64) : wordAt inner.memory current=wordAt source.memory current:=by
    rw [finalTags current (members current live) nonzero]
    unfold wordAt
    rw [memory current (regions.footprint_before graph nodeLower heap.toNat current (.header current live nonzero))]
  have restoredLocals : (restore source "br" inner).locals=source.locals.update (ofString "r",.val (.word root)):=by
    change HolFiniteMapExact.resVarEq inner.locals (ofString "br",source.locals.lookup (ofString "br"))=_
    rw [resultLocals,localsEq]
    change (restore source "br" (QueryBranch.bind (QueryBranch.bind source "br" heap) "r" root)).locals=_
    rw [restore_bind_other source _ "br" "r" root (by decide),restore_bound]
    rfl
  have spent : source.clock-inner.clock≤239:=by omega
  rw [endpoint]
  exact ⟨root,restoredLocals,finalDomain.trans domainEq,finalEndian.trans endianEq,finalCode.trans codeEq,spent,olderMemory,tags,
    finalHeap,finalHeapCell,finalArena,finalAligned,grows.trans finalGrows,next,(fun current live=>finalMembers current (members current live)),rootMember,
    nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.extension_split_normal
