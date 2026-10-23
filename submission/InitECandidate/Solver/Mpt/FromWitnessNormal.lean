import InitECandidate.Solver.Mpt.FromWitnessProgram
import InitECandidate.Solver.Mpt.FromWitnessOutput
import InitECandidate.Solver.Mpt.WitnessRootPathNormal
import InitECandidate.Solver.Mpt.WitnessRootGlobals
import InitECandidate.Solver.Mpt.TrieGraphPathErase
import InitECandidate.Solver.Input.TailCallNormal

namespace InitECandidate.Solver.Mpt.FromWitness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors WitnessMaterialize WitnessCore

/-- Whole unchanged245 follows its actual witness decode and tail map
constructor. The returned header follows every decoded node and path;
no future graph or successful allocation is assumed. -/
theorem body_normal (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db incoming rootHash flag emptyRoot : BitVec 64) (boundary : RootBoundary input source)
    (little : source.be=false) (installed : Input.OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word rootHash)))
    (flagCell : source.locals.lookup (ofString "secured")=some (.val (.word flag)))
    (emptyCell : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word incoming))) (heapLower : 2713731432≤incoming.toNat)
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    Nonempty (Output input source target value db incoming flag) := by
  obtain ⟨callee,called,entryDb,entryRoot⟩:=WitnessDecodeRoot.environment source.code.lookup db rootHash (WitnessDecodeRoot.original_code source.code installed)
  rw [body_shape] at normal
  obtain ⟨_funded,decoded,returned,inner,decodeRun,_checked,continued,endpoint⟩:=Input.CallNormal.scoped_normal source target "root" .one
    (ofString "decode_witness_to_mpt") decodeArguments _ WitnessDecodeRoot.body tail callee .one (decode_arguments source db rootHash dbCell rootCell) called value normal
  let entry:=callEntryStateHOLFinite source callee
  have entryBoundary:=boundary.erase_frame input source entry rfl (entryDb.trans dbCell.symm)
  have entryScratch:=scratch.of_fields source entry 2713714688#64 2701135872#64 rfl rfl
  have decodedOutput:=WitnessDecodeRoot.path_body_normal_prefix_scratch input entry decoded db incoming rootHash emptyRoot entryBoundary little installed
    entryDb entryRoot emptyCell heapCell heapLower entryScratch returned decodeRun
  let current:=Input.CallNormal.continuationEntry source decoded "root" returned
  have currentOutput:=decodedOutput.1.of_erase input incoming.toNat db decoded current returned rfl
  obtain ⟨map,node,returnedEq,mapCell,registry,model,member⟩:=currentOutput.2
  obtain ⟨physicalHeap,physicalRoot,physicalAnswer,physicalCell,mapArena,mapAligned,mapGrows,_oldScratch,frozen,_owned⟩:=currentOutput.1
  have sameHeap : physicalHeap=map:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (physicalCell.symm.trans mapCell)))
  subst physicalHeap
  have rootLocal : current.locals.lookup (ofString "root")=some (.val (.word node)):=
    (Input.CallNormal.continuation_lookup_same source decoded "root" returned).trans (congrArg some returnedEq)
  have flagLocal : current.locals.lookup (ofString "secured")=some (.val (.word flag)):=
    (Input.CallNormal.continuation_lookup_other source decoded "root" "secured" returned (by decide)).trans flagCell
  have newArgs : evalListHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) newArguments=some (NewTrie.values node flag):=by
    simp [newArguments,NewTrie.values,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,rootLocal,flagLocal]
  have decoderFields:=Input.evaluation_fields entry decoded WitnessDecodeRoot.body (some (.returned returned)) decodeRun
  have currentInstalled : Input.OriginalCode.Installed current.code:=by change Input.OriginalCode.Installed decoded.code; rw [decoderFields.2.2.2]; exact installed
  have currentDomain : current.memaddrs=InitE.ordinaryDomain:=decoderFields.1.trans scratch.domain
  obtain ⟨newCallee,newCalled,newRoot,newFlag⟩:=NewTrie.environment current.code.lookup node flag (NewTrie.original_code current.code currentInstalled)
  obtain ⟨_newFunded,built,newRun,_newChecked,tailEnd⟩:=Input.CallNormal.tail_callee_return current inner (ofString "mpt_new") newArguments _ NewTrie.body newCallee .one newArgs newCalled value continued
  obtain ⟨room,valueEq,newFrame⟩:=NewTrie.normal (callEntryStateHOLFinite current newCallee) built map node flag currentInstalled newRoot newFlag mapCell currentDomain mapArena mapAligned value newRun
  have finalFrame : Input.LocalEffects.erase target=Input.LocalEffects.erase (NewTrie.post current map node flag):=by
    rw [endpoint,tailEnd]
    have projected:=congrArg Input.LocalEffects.erase newFrame
    exact projected
  obtain ⟨_sourceFields,postGraph,postSame,postRegions,postDisjoint,⟨postValues⟩,postPaths,postPathRegions,postSeparated,postHeader⟩:=
    NewTrie.post_graph current map node flag room mapAligned registry.graph 1024 incoming.toNat incoming.toNat (WitnessValue db)
      registry.values registry.regions registry.disjoint model.bytes model.regions model.separated member
  let after:=NewTrie.post current map node flag
  obtain ⟨next,same,nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated⟩:=postGraph.after_erase after target 1024 incoming.toNat
    (PersistentAlloc.rounded map 16#64).toNat incoming.toNat (PersistentAlloc.rounded map 16#64).toNat (WitnessValue db)
      postValues postRegions postDisjoint postPaths postPathRegions postSeparated finalFrame
  have finalMemory:=Input.LocalEffects.memory_of_erase after target finalFrame
  have finalGlobals:=congrArg PanSemStateFiniteExact.globals finalFrame
  change target.globals=after.globals at finalGlobals
  have finalDomain:=congrArg PanSemStateFiniteExact.memaddrs finalFrame
  change target.memaddrs=current.memaddrs at finalDomain
  have finalEndian:=congrArg PanSemStateFiniteExact.be finalFrame
  change target.be=current.be at finalEndian
  have growth:=PersistentAlloc.guards map 16#64 room.upper
  have finalHeap : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded map 16#64))):=by
    rw [finalGlobals]
    simp [after,NewTrie.post,HolFiniteMapExact.update,FUPDATE]
  have decoderGlobals : HeapGlobals source current:=by
    intro name other
    by_cases isScratch : name=ofString "scratch_ptr"
    · subst name
      exact decodedOutput.2.2.trans scratch.cursorGlobal.symm
    · have kept:=WitnessDecodeRoot.globals name source.code installed other isScratch entry rfl
      rw [decodeRun] at kept
      exact congrArg Prod.snd kept
  have currentPrefix : Stack.StablePrefix source current incoming.toNat:=decodedOutput.2.1
  have finalPrefix : Stack.StablePrefix source target incoming.toNat:=by
    intro query lower upper
    exact (congrFun finalMemory query).trans ((NewTrie.post_older current map node flag query room (upper.trans_le mapGrows)).trans (currentPrefix query lower upper))
  have finalFrozen:=frozen.frame input (bind current "db" db) (bind target "db" db) incoming.toNat finalDomain finalEndian
    ((bind_lookup_same target "db" db).trans (bind_lookup_same current "db" db).symm)
    (by intro query lower upper; exact (congrFun finalMemory query).trans (NewTrie.post_older current map node flag query room (upper.trans_le mapGrows)))
  exact ⟨{
    map:=map
    root:=node
    heap:=PersistentAlloc.rounded map 16#64
    answer:=valueEq
    domain:=finalDomain.trans decoderFields.1
    endian:=finalEndian.trans decoderFields.2.1
    code:=by have projected:=congrArg PanSemStateFiniteExact.code finalFrame; exact projected.trans decoderFields.2.2.2
    globalsNonHeap:=by
      intro name other
      rw [finalGlobals]
      exact (HeapGlobals.update current (PersistentAlloc.rounded map 16#64) name other).trans (decoderGlobals name other)
    heapCell:=finalHeap
    heapArena:=⟨by have lower:=room.lower; have grows:=growth.2.2.1; omega,by have upper:=growth.2.2.2.1; omega⟩
    heapAligned:=growth.2.2.2.2
    mapGrows:=mapGrows
    headerBefore:=growth.2.2.1
    graph:=next
    values:=nextValues
    regions:=nextRegions
    disjoint:=nextDisjoint
    paths:=nextPaths
    pathRegions:=nextPathRegions
    separated:=nextSeparated
    header:=postHeader.of_erase after target postGraph next map node flag same finalFrame
    frozen:=finalFrozen
    memory:=finalPrefix }⟩

end InitECandidate.Solver.Mpt.FromWitness

#print axioms InitECandidate.Solver.Mpt.FromWitness.body_normal
