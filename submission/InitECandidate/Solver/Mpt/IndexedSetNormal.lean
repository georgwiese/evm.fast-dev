import InitECandidate.Solver.Mpt.IndexedSetCost
import InitECandidate.Solver.Mpt.InsertAssignedPaths
import InitECandidate.Solver.Mpt.SetRootStore
import InitECandidate.Solver.Mpt.TrieGraphPathBand
import InitECandidate.Solver.Input.NormalWordDeclaration

namespace InitECandidate.Solver.Mpt.IndexedSet
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Actual setter output for the indexed builder. Its live nodes/paths
remain beyond the original cutoff; only its earlier root header may change. -/
structure Output (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (m incoming : BitVec 64) (cutoff limit : Nat)
    (property : BitVec 64→BitVec 64→Prop := fun _ _=>True) where
  root : BitVec 64
  heap : BitVec 64
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  code : target.code=source.code
  globals : HeapGlobals source target
  heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapAligned : heap.toNat%8=0
  grows : incoming.toNat≤heap.toNat
  rootStored : target.memory m=.word root
  older : ∀ query : BitVec 64,query.toNat<cutoff→query≠m→target.memory query=source.memory query
  graph : TrieWalk.Graph target.memory target.memaddrs
  member : graph.valid root
  rootUncached : TrieWalk.Uncached target.memory root
  rootActive : root≠0#64
  values : TrieWalk.Values graph limit property
  regions : graph.Regions cutoff heap.toNat
  disjoint : graph.Disjoint
  paths : graph.PathBytes target.be
  pathRegions : graph.PathRegions cutoff heap.toNat
  separated : graph.PathSeparated

/-- A real normal suffix derives the returned root, actual header store
and complete retained graph. No later row or mutation is assumed normal. -/
theorem Converted.suffix_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {m pointer size : BitVec 64} {cutoff limit : Nat} {property : BitVec 64→BitVec 64→Prop}
    (data : Converted source m pointer size cutoff limit property) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source SetTrie.afterKey=(some (.returned value),target)) :
    value=.val (.word 0#64) ∧ Nonempty (Output source target m data.heap cutoff limit property) := by
  have mapped : source.memaddrs m:=by
    simpa only [byteAddress,BitVec.add_zero] using AllocatedBytes.word_mapped source m 16 0 data.domain data.headerArena (by decide) data.headerAligned (by decide)
  have read : eval source SetTrie.rootExpression=some (.val (.word data.root)):=by
    simp [eval,SetTrie.rootExpression,addConst,localVar,evalHOLExact,evalListHOLExact,toExact,data.mCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped,data.rootStored]
  rw [SetTrie.mutation_shapes.1] at normal
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_return_word source target "root" SetTrie.rootExpression data.root SetTrie.afterRoot value read normal
  let ready:=bind source "root" data.root
  have rootCell : ready.locals.lookup (ofString "root")=some (.val (.word data.root)):=bind_lookup_same _ _ _
  have nkCell : ready.locals.lookup (ofString "nk")=some (.rStruct [.val (.word data.key),.val (.word data.length)]):=
    (bind_lookup_other _ "root" "nk" data.root (by decide)).trans data.nkCell
  have pointerCell : ready.locals.lookup (ofString "vptr")=some (.val (.word pointer)):=
    (bind_lookup_other _ "root" "vptr" data.root (by decide)).trans data.pointerCell
  have sizeCell : ready.locals.lookup (ofString "vlen")=some (.val (.word size)):=
    (bind_lookup_other _ "root" "vlen" data.root (by decide)).trans data.sizeCell
  have chosen : evaluateHOLFiniteState ready SetTrie.afterRoot=evaluateHOLFiniteState ready (.seq SetTrie.insertCall SetTrie.footer):=by
    rw [SetTrie.mutation_shapes.2.1,evaluateHOLFiniteState_seq_line780,
      SetTrie.insert_selected ready pointer size pointerCell sizeCell data.pointerActive data.sizeActive,evaluateHOLFiniteState_seq_line780]
  change evaluateHOLFiniteState ready SetTrie.afterRoot=(some (.returned value),inner) at continued
  rw [chosen] at continued
  have safe : Input.LocalPrefix (ofString "m") SetTrie.insertCall:=
    .call (some (ofString "root")) _ _ (by intro name same; cases same; decide)
  obtain ⟨middle,insertRun,footerRun⟩:=Input.sequence_returned ready inner SetTrie.insertCall SetTrie.footer value
    (fun returned=>(safe.summary_full ready).2.1 returned) continued
  have args : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) SetTrie.insertArguments=
      some (Insert.values data.root data.key data.length 0#64 pointer size):=by
    simp [SetTrie.insertArguments,Insert.values,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,rootCell,nkCell,pointerCell,sizeCell]
  obtain ⟨root,localsEq,⟨output⟩⟩:=Insert.assigned_path_normal ready middle data.heap data.root data.key 0#64 data.length pointer size data.graph
    limit cutoff cutoff property data.values data.regions data.disjoint data.paths data.pathRegions data.separated data.query data.member
    (by simp) data.small data.payload data.extra data.empty data.floor data.domain data.installed data.heapCell data.heapArena data.heapAligned
    (ofString "root") SetTrie.insertArguments args insertRun
  have currentM : middle.locals.lookup (ofString "m")=some (.val (.word m)):=by
    rw [localsEq]
    simpa [HolFiniteMapExact.update,FUPDATE,ofString,ready,QueryBranch.bind,setVarHOLFinite] using data.mCell
  have currentRoot : middle.locals.lookup (ofString "root")=some (.val (.word root)):=by
    rw [localsEq]
    simp [HolFiniteMapExact.update,FUPDATE]
  have currentMapped : middle.memaddrs m:=by rw [output.domain]; exact mapped
  have executed:=SetTrie.footer_execute middle m root currentM currentRoot currentMapped
  have compared:=footerRun.symm.trans executed
  have answer : value=.val (.word 0#64):=by
    have observed:=congrArg Prod.fst compared
    simpa using observed
  have innerEq : inner=emptyLocalsHOLFinite (SetTrie.rootStored middle m root):=congrArg Prod.snd compared
  let finished:=emptyLocalsHOLFinite (SetTrie.rootStored middle m root)
  have band (query : BitVec 64) (above : cutoff≤query.toNat) (_before : query.toNat<output.heap.toNat) : finished.memory query=middle.memory query:=by
    have different : query≠m:=by intro same; subst query; have before:=data.headerBefore; omega
    exact if_neg different
  obtain ⟨graph,same,regions,disjoint,values,paths,pathRegions,separated⟩:=output.next.after_path_band middle finished limit cutoff cutoff output.heap.toNat cutoff property
    output.values output.regions output.disjoint output.paths output.pathRegions output.separated data.cutoffAligned (Nat.le_refl _) (Nat.le_refl _) rfl rfl band
  have rootClean:=(output.next.cache_of_band cutoff output.heap.toNat output.regions band).uncached output.next root output.rootMember output.rootUncached
  rw [endpoint,innerEq]
  refine ⟨answer,⟨{
    root:=root,heap:=output.heap,domain:=output.domain,endian:=output.endian,code:=output.code,globals:=output.globalsNonHeap
    heapCell:=output.heapCell,heapArena:=output.heapArena,heapAligned:=output.heapAligned,grows:=output.heapGrows
    rootStored:=by change StoreWord.put middle.memory m root m=.word root; exact if_pos rfl
    older:=?_
    graph:=graph,member:=by rw [same]; exact output.rootMember
    rootUncached:=rootClean,rootActive:=output.rootActive
    values:=Classical.choice values
    regions:=regions,disjoint:=disjoint,paths:=paths,pathRegions:=pathRegions,separated:=separated }⟩⟩
  intro query before different
  exact (if_neg different).trans (output.olderPrefix query before)

/-- The whole genuine current setter returns zero, installs its registered
root and retains all older rows except that root word. The conversion and
insertion frames come only from these same actual normal calls. -/
theorem body_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {m rawKey pointer size : BitVec 64} {byteLength cutoff limit : Nat} {property : BitVec 64→BitVec 64→Prop}
    (data : Entry source m rawKey byteLength pointer size cutoff limit property) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source SetTrie.body=(some (.returned value),target)) :
    value=.val (.word 0#64) ∧ Nonempty (Output source target m data.heap cutoff limit property) := by
  obtain ⟨callee,called,mLocal,keyLocal,lengthLocal⟩:=NibbleKey.environment source.code.lookup m rawKey (BitVec.ofNat 64 byteLength)
    (NibbleKey.original_code source.code data.installed)
  have args:=SetTrie.key_arguments source m rawKey byteLength data.mCell data.keyCell data.lengthCell
  rw [SetTrie.body_shape] at normal
  obtain ⟨funded,child,returned,inner,run,checked,continued,endpoint⟩:=Input.CallNormal.scoped_normal source target "nk" NibbleKey.returnShape
    (ofString "mpt_nibble_key") SetTrie.keyArguments _ NibbleKey.body SetTrie.afterKey callee NibbleKey.returnShape args called value normal
  let current:=Input.CallNormal.continuationEntry source child "nk" returned
  have reached : Input.CallPrefix.Reaches source (.scoped (ofString "nk") NibbleKey.returnShape (ofString "mpt_nibble_key") SetTrie.keyArguments) current:=
    .scoped source (ofString "nk") NibbleKey.returnShape (ofString "mpt_nibble_key") SetTrie.keyArguments _ NibbleKey.body callee NibbleKey.returnShape
      returned child args called (by omega) run checked
  obtain ⟨converted⟩:=data.after_key reached
  obtain ⟨answer,⟨output⟩⟩:=converted.suffix_normal value continued
  have flagMapped : source.memaddrs (m+8#64):=by
    simpa only [byteAddress] using AllocatedBytes.word_mapped source m 16 8 data.domain data.headerArena (by decide) data.headerAligned (by decide)
  obtain ⟨arena,nk,saved,view,price,frame,memory⟩:=NibbleKey.scoped_normal (ofString "nk") SetTrie.keyArguments m rawKey data.heap byteLength
    data.small data.installed data.domain data.little args flagMapped data.flagStored data.heapCell data.heapArena data.heapAligned data.inputArena data.inputBefore reached
  let amount:=BitVec.ofNat 64 (2*byteLength)
  let finalHeap:=PersistentAlloc.rounded data.heap amount
  have amountNumber : amount.toNat=2*byteLength:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have small:=data.small; omega)]
  have numeric:=NodeConstructor.rounded_ordinary data.heap amount (by rw [amountNumber]; exact arena.upper)
  have grows : data.heap.toNat≤finalHeap.toNat:=by
    change data.heap.toNat≤(PersistentAlloc.rounded data.heap amount).toNat
    omega
  have globalsEq:=congrArg PanSemStateFiniteExact.globals frame
  change current.globals=(PersistentAlloc.post source data.heap amount).globals at globalsEq
  have currentHeap : current.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)):=by
    rw [globalsEq]
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,finalHeap]
  have convertedHeap : converted.heap=finalHeap:=by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using converted.heapCell.symm.trans currentHeap
  have globals : HeapGlobals source current:=by
    intro name other
    rw [globalsEq]
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm other]
  have domainEq:=Input.MemoryMetadata.domain frame
  change current.memaddrs=source.memaddrs at domainEq
  have endianEq:=Input.MemoryMetadata.endian frame
  change current.be=source.be at endianEq
  have codeEq:=Input.MemoryMetadata.code frame
  change current.code=source.code at codeEq
  have totalGrows : data.heap.toNat≤output.heap.toNat:=by
    have convertedGrows : data.heap.toNat≤converted.heap.toNat:=by rw [convertedHeap]; exact grows
    exact Nat.le_trans convertedGrows output.grows
  rw [endpoint]
  refine ⟨answer,⟨{
    root:=output.root,heap:=output.heap,domain:=output.domain.trans domainEq,endian:=output.endian.trans endianEq,code:=output.code.trans codeEq
    globals:=fun name other=>(output.globals name other).trans (globals name other)
    heapCell:=output.heapCell,heapArena:=output.heapArena,heapAligned:=output.heapAligned,grows:=totalGrows,rootStored:=output.rootStored
    older:=?_
    graph:=output.graph,member:=output.member,rootUncached:=output.rootUncached,rootActive:=output.rootActive,values:=output.values,regions:=output.regions,disjoint:=output.disjoint
    paths:=output.paths,pathRegions:=output.pathRegions,separated:=output.separated }⟩⟩
  intro query before different
  exact (output.older query before different).trans (memory query (Or.inl (Nat.lt_of_lt_of_le before data.floor)))

end InitECandidate.Solver.Mpt.IndexedSet

#print axioms InitECandidate.Solver.Mpt.IndexedSet.Converted.suffix_normal

#print axioms InitECandidate.Solver.Mpt.IndexedSet.body_normal
