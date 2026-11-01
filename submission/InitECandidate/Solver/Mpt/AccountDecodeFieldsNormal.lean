import InitECandidate.Solver.Mpt.AccountDecodeCall
import InitECandidate.Solver.Input.IgnoredCallData
import InitECandidate.Solver.Mpt.AccountAfterFieldsNormal
import InitECandidate.Solver.Mpt.AccountImage
import InitECandidate.Solver.Mpt.AccountDecodeCost
import InitECandidate.Solver.Mpt.AccountDecodeNormalPrefix
import InitECandidate.Solver.Mpt.AccountAfterDecodeNormal
import InitECandidate.Solver.Mpt.AccountFieldsNormal

namespace InitECandidate.Solver.Mpt.AccountDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 10000 in
/-- A real normal complete original account body reaches afterFields with
its actual four decoded values. Both validation passes, record allocation,
count guard and every item call are included in the derived state/frame. -/
theorem body_fields (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit out : BitVec 64) (cutoff : Nat)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (output : Output out) (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    ∃ (header payload : BitVec 64) (a b c d : Rlp.ListItem) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      header.toNat+payload.toNat=length.toNat ∧ header.toNat≤9 ∧ heap.toNat+64≤33806089496 ∧ Nonempty (FieldResults ready (pointer+header) a b c d) ∧
      FieldsView ready heap (pointer+header) payload cursor limit out cutoff [a,b,c,d] ∧
      ready.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 64#64))) ∧
      ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧ ready.code=source.code ∧
      (∀ query : BitVec 64,cursor.toNat≤query.toNat → query.toNat<heap.toNat ∨ heap.toNat+64≤query.toNat → ready.memory query=source.memory query) ∧
      evaluateHOLFiniteState ready afterFields=(some (.returned returned),inner) ∧
      emptyLocalsHOLFinite post=emptyLocalsHOLFinite inner := by
  have fits : pointer.toNat+length.toNat<2^64 := by omega
  obtain ⟨answer,decoded,decodedPost,complete,decodedArena,decodedAbove,decodedDomain,decodedEndian,decodedCode,decodedHeap,itemCell,decodedOutput,decodedRun,decodedFrame⟩ :=
    body_decode_prefix source post pointer length cursor limit out pointerCell lengthCell outputCell arena fits installed returned normal
  have decodedInstalled : Input.OriginalCode.Installed decoded.code := by rw [decodedCode]; exact installed
  obtain ⟨header,payload,items,fieldsEntry,fieldsPost,extent,head,itemEq,lengthFour,recordRoom,fieldsView,fieldsHeap,fieldsDomain,fieldsEndian,fieldsCode,fieldsMemory,fieldsRun,fieldsFrame⟩ :=
    after_decode_fields decoded decodedPost pointer length heap cursor limit out cutoff answer itemCell complete decodedOutput decodedArena
      (decodedHeap.trans heapGlobal) heapBound before sizeBound aligned scratchBelow inputAbove output decodedInstalled returned decodedRun
  obtain ⟨a,b,c,d,itemsEq⟩ := List.length_eq_four.mp lengthFour
  subst items
  have fieldsInstalled : Input.OriginalCode.Installed fieldsEntry.code := by rw [fieldsCode]; exact decodedInstalled
  obtain ⟨ready,inner,results,view,above,domain,endian,codeEq,heapEq,tailRun,tailFrame⟩ :=
    fields_normal fieldsEntry fieldsPost heap (pointer+header) payload cursor limit out cutoff a b c d fieldsView fieldsInstalled returned fieldsRun
  refine ⟨header,payload,a,b,c,d,ready,inner,extent,head,recordRoom,results,view,heapEq.trans fieldsHeap,
    domain.trans (fieldsDomain.trans decodedDomain),endian.trans (fieldsEndian.trans decodedEndian),codeEq.trans (fieldsCode.trans decodedCode),?_,tailRun,
    decodedFrame.trans (fieldsFrame.trans tailFrame)⟩
  intro query beyond outside
  exact (above query beyond).trans ((fieldsMemory query beyond outside).trans (decodedAbove query beyond))

end InitECandidate.Solver.Mpt.AccountDecode

#print axioms InitECandidate.Solver.Mpt.AccountDecode.body_fields

namespace InitECandidate.Solver.Mpt.AccountDecode.Current
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A real current normal account decode reaches its output phase with
four actual field values, exactly64 bytes of list records and every earlier
word protected. No old low-scratch geometry is required. -/
theorem body_fields (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap out : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (arena : Rlp.LiveArena source)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (before : length≠0#64 → pointer.toNat+length.toNat≤heap.toNat)
    (sizeBound : 16*length.toNat<2^64) (output : Output out)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    ∃ (header payload : BitVec 64) (a b c d : Rlp.ListItem) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      header.toNat+payload.toNat=length.toNat ∧ header.toNat≤9 ∧ heap.toNat+64≤2952790016 ∧
      Nonempty (FieldResults ready (pointer+header) a b c d) ∧ FieldsView ready heap (pointer+header) payload out [a,b,c,d] ∧
      Input.MemoryMetadata.erase ready=Input.MemoryMetadata.erase (PersistentAlloc.post source heap 64#64) ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → ready.memory query=source.memory query) ∧
      evaluateHOLFiniteState ready afterFields=(some (.returned returned),inner) ∧
      emptyLocalsHOLFinite post=emptyLocalsHOLFinite inner := by
  have fits : pointer.toNat+length.toNat<2^64:=by
    by_cases empty : length=0#64
    · rw [empty]; simpa using pointer.isLt
    · have prior:=before empty; have bound:=heap.isLt; omega
  obtain ⟨answer,decoded,decodedPost,complete,decodedFrame,itemCell,decodedOutput,decodedRun,decodedRestore⟩:=
    body_decode_prefix source post pointer length out pointerCell lengthCell outputCell arena fits installed returned normal
  have decodedArena:=arena.of_metadata decodedFrame.metadata
  have decodedGlobals:=congrArg PanSemStateFiniteExact.globals decodedFrame.metadata
  change decoded.globals=source.globals at decodedGlobals
  have decodedHeap : decoded.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by
    rw [decodedGlobals]; exact heapGlobal
  have nonempty : length≠0#64:=by
    intro empty
    obtain ⟨h,p,f,eq,head,positive,extent,rest⟩:=complete
    rw [empty] at extent
    change h.toNat+p.toNat=0 at extent
    omega
  obtain ⟨header,payload,items,fieldsEntry,fieldsPost,extent,head,itemEq,lengthFour,recordRoom,fieldsView,fieldsMetadata,fieldsMemory,fieldsRun,fieldsRestore⟩:=
    after_decode_fields decoded decodedPost pointer length heap out answer itemCell complete decodedOutput decodedArena decodedHeap heapBound
      (before nonempty) sizeBound output decodedArena.code returned decodedRun
  obtain ⟨a,b,c,d,itemsEq⟩:=List.length_eq_four.mp lengthFour
  subst items
  obtain ⟨ready,inner,results,view,fieldFrame,tailRun,tailRestore⟩:=
    fields_normal fieldsEntry fieldsPost heap (pointer+header) payload out a b c d fieldsView returned fieldsRun
  have inherited:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>PersistentAlloc.post state heap 64#64) decodedFrame.metadata
  change Input.MemoryMetadata.erase (PersistentAlloc.post decoded heap 64#64)=
    Input.MemoryMetadata.erase (PersistentAlloc.post source heap 64#64) at inherited
  refine ⟨header,payload,a,b,c,d,ready,inner,extent,head,recordRoom,results,view,
    fieldFrame.metadata.trans (fieldsMetadata.trans inherited),?_,tailRun,decodedRestore.trans (fieldsRestore.trans tailRestore)⟩
  intro query earlier
  exact (fieldFrame.outside query (Or.inl (by omega))).trans
    ((fieldsMemory query earlier).trans (decodedFrame.outside query (Or.inl (by omega))))

end InitECandidate.Solver.Mpt.AccountDecode.Current

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Current.body_fields

namespace InitECandidate.Solver.Mpt.AccountDecode.Current
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Complete real normal current account decoding. The actual four parsed
fields and output guards produce the physical account/reference image;
only the fresh records, output and high scratch may affect earlier memory. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap out emptyRoot emptyHash : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (outputCell : source.locals.lookup (ofString "acct_out")=some (.val (.word out)))
    (arena : Rlp.LiveArena source)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016)
    (before : length≠0#64 → pointer.toNat+length.toNat≤heap.toNat)
    (inputLower : length≠0#64 → 2701131776≤pointer.toNat)
    (sizeBound : 16*length.toNat<2^64)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (output : Output out) (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ Nonempty (Image post out) ∧ Rlp.LiveArena post ∧ heap.toNat+64≤2952790016 ∧
      Input.MemoryMetadata.erase post=Input.MemoryMetadata.erase (PersistentAlloc.post source heap 64#64) ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → query.toNat<out.toNat ∨ out.toNat+56≤query.toNat → post.memory query=source.memory query) ∧
      source.clock-post.clock≤191*length.toNat+261 := by
  obtain ⟨header,payload,a,b,c,d,ready,inner,extent,head,recordRoom,⟨results⟩,view,readyMetadata,prefixMemory,tailRun,restored⟩:=
    body_fields source post pointer length heap out pointerCell lengthCell outputCell arena heapGlobal heapBound before sizeBound output installed returned normal
  have readyInstalled : Input.OriginalCode.Installed ready.code:=view.arena.code
  have readyGlobals:=congrArg PanSemStateFiniteExact.globals readyMetadata
  change ready.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 64#64))) at readyGlobals
  have currentRoot : ready.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)):=by
    rw [readyGlobals]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "heap_ptr"≠ofString "empty_trie_root" from by decide] using rootGlobal
  have currentHash : ready.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)):=by
    rw [readyGlobals]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "heap_ptr"≠ofString "empty_code_hash" from by decide] using hashGlobal
  obtain ⟨h0,p0,f0,value0,head0,positive0,bound0,binary0,list0⟩:=results.valid0
  obtain ⟨h1,p1,f1,value1,head1,positive1,bound1,binary1,list1⟩:=results.valid1
  obtain ⟨h2,p2,f2,value2,head2,positive2,bound2,binary2,list2⟩:=results.valid2
  obtain ⟨h3,p3,f3,value3,head3,positive3,bound3,binary3,list3⟩:=results.valid3
  have cell0:=results.cell0
  have cell1:=results.cell1
  have cell2:=results.cell2
  have cell3:=results.cell3
  rw [value0] at cell0
  rw [value1] at cell1
  rw [value2] at cell2
  rw [value3] at cell3
  let base0:=Rlp.Slices.itemPointer (pointer+header) [a,b,c,d] 0
  let base1:=Rlp.Slices.itemPointer (pointer+header) [a,b,c,d] 1
  let base2:=Rlp.Slices.itemPointer (pointer+header) [a,b,c,d] 2
  let base3:=Rlp.Slices.itemPointer (pointer+header) [a,b,c,d] 3
  obtain ⟨result,stringFlags,nonceBound,balanceBound,rootWidth,hashWidth,window,rootStored,hashStored⟩:=
    after_fields_normal ready inner out base0 h0 p0 f0 base1 h1 p1 f1 base2 h2 p2 f2 base3 h3 p3 f3 emptyRoot emptyHash
      view.outputCell cell0 cell1 cell2 cell3 currentRoot currentHash output view.arena.domain readyInstalled returned tailRun
  have countBound:=Rlp.ListItems.count_le ready (pointer+header) payload.toNat [a,b,c,d] view.itemsModel
  change 4≤payload.toNat at countBound
  have nonempty : length≠0#64:=by
    intro empty
    rw [empty] at extent
    change header.toNat+payload.toNat=0 at extent
    omega
  have payloadLower : 2701131776≤(pointer+header).toNat:=by
    have lower:=inputLower nonempty
    have prior:=before nonempty
    rw [BitVec.toNat_add_of_lt (by omega)]
    omega
  have selectedRootArena:=view.payload_arena ready heap (pointer+header) payload out [a,b,c,d] payloadLower 2 c rfl h2 p2 bound2
  have selectedHashArena:=view.payload_arena ready heap (pointer+header) payload out [a,b,c,d] payloadLower 3 d rfl h3 p3 bound3
  have rootRegion : AllocatedBytes.Arena (if p2=0#64 then emptyRoot else base2+h2) 32:=by
    by_cases zero : p2=0#64
    · simpa only [if_pos zero] using rootArena
    · have width:=rootWidth.resolve_left zero
      rw [if_neg zero]
      simpa [width,base2] using selectedRootArena
  have hashRegion : AllocatedBytes.Arena (if p3=0#64 then emptyHash else base3+h3) 32:=by
    by_cases zero : p3=0#64
    · simpa only [if_pos zero] using hashArena
    · have width:=hashWidth.resolve_left zero
      rw [if_neg zero]
      simpa [width,base3] using selectedHashArena
  have finalMemory:=congrArg PanSemStateFiniteExact.memory restored
  change post.memory=inner.memory at finalMemory
  have tailMetadata:=after_fields_metadata ready.code readyInstalled ready rfl
  rw [tailRun] at tailMetadata
  change Input.MemoryMetadata.erase inner=Input.MemoryMetadata.erase ready at tailMetadata
  have restoredMetadata:=congrArg Input.MemoryMetadata.erase restored
  change Input.MemoryMetadata.erase post=Input.MemoryMetadata.erase inner at restoredMetadata
  have finalTailMetadata:=restoredMetadata.trans tailMetadata
  have nextArena:=view.arena.of_metadata finalTailMetadata
  have image : Image post out:=⟨output,nextArena.domain,_,_,by rw [finalMemory]; exact rootStored,by rw [finalMemory]; exact hashStored,rootRegion,hashRegion⟩
  have price:=body_cost source pointer length heap out pointerCell lengthCell outputCell arena heapGlobal heapBound before sizeBound output installed
  rw [normal] at price
  refine ⟨result,⟨image⟩,nextArena,recordRoom,finalTailMetadata.trans readyMetadata,?_,price⟩
  intro query earlier outsideOutput
  rw [finalMemory]
  exact (window query outsideOutput).trans (prefixMemory query earlier)

end InitECandidate.Solver.Mpt.AccountDecode.Current

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Current.body_normal

namespace InitECandidate.Solver.Mpt.AccountDecode.Current
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- The real ignored caller transfers the normal account image and
allocation/frame guarantee through the actual ABI and local restoration. -/
theorem ignored_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap out emptyRoot emptyHash : BitVec 64)
    (arena : Rlp.LiveArena source)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016)
    (before : length≠0#64 → pointer.toNat+length.toNat≤heap.toNat)
    (inputLower : length≠0#64 → 2701131776≤pointer.toNat)
    (sizeBound : 16*length.toNat<2^64)
    (rootGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (hashGlobal : source.globals.lookup (ofString "empty_code_hash")=some (.val (.word emptyHash)))
    (rootArena : AllocatedBytes.Arena emptyRoot 32) (hashArena : AllocatedBytes.Arena emptyHash 32)
    (output : Output out) (installed : Input.OriginalCode.Installed source.code) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values pointer length out))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "decode_account_from_leaf") arguments)=(none,post)) :
    1≤source.clock ∧ Nonempty (Image post out) ∧ Rlp.LiveArena post ∧ heap.toNat+64≤2952790016 ∧
      Input.MemoryMetadata.erase post=Input.MemoryMetadata.erase (PersistentAlloc.post source heap 64#64) ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → query.toNat<out.toNat ∨ out.toNat+56≤query.toNat → post.memory query=source.memory query) ∧
      source.clock-post.clock≤191*length.toNat+262 := by
  obtain ⟨positive,actualValues,actualBody,actualCallee,shape,target,returned,actualArgs,called,bodyRun,checked,postEq,fields⟩:=
    Input.CallNormal.ignored_data source post (ofString "decode_account_from_leaf") arguments normal
  have valuesEq:=Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  obtain ⟨callee,expected,p,n,a⟩:=environment source.code.lookup pointer length out (original_code source.code installed)
  rw [expected] at called
  simp only [Option.some.injEq,Prod.mk.injEq] at called
  rcases called with ⟨rfl,rfl,rfl⟩
  let entry:=callEntryStateHOLFinite source callee
  obtain ⟨result,⟨image⟩,nextArena,room,metadata,window,price⟩:=body_normal entry target pointer length heap out emptyRoot emptyHash p n a
    (arena.of_frame rfl) heapGlobal heapBound before inputLower sizeBound rootGlobal hashGlobal rootArena hashArena output installed returned bodyRun
  have inherited : Input.MemoryMetadata.erase (PersistentAlloc.post entry heap 64#64)=Input.MemoryMetadata.erase (PersistentAlloc.post source heap 64#64):=rfl
  have cost:=call_cost source pointer length heap out arena heapGlobal heapBound before sizeBound output installed (some none) arguments args
  change source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "decode_account_from_leaf") arguments)).2.clock≤191*length.toNat+262 at cost
  rw [normal] at cost
  refine ⟨positive,?_,?_,room,?_,?_,cost⟩
  · rw [postEq]
    exact ⟨Image.of_agreement target _ out image rfl rfl rfl⟩
  · rw [postEq]
    exact nextArena.of_frame rfl
  · rw [postEq]
    exact metadata.trans inherited
  · rw [postEq]
    exact window

end InitECandidate.Solver.Mpt.AccountDecode.Current

#print axioms InitECandidate.Solver.Mpt.AccountDecode.Current.ignored_normal
