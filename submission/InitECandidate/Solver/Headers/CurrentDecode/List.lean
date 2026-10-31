import InitECandidate.Solver.Headers.CurrentDecode.Top
import InitECandidate.Solver.Rlp.CurrentSlicesCall

namespace InitECandidate.Solver.Headers.CurrentDecode
open Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- A real normal header return derives its complete encoded list, counted
physical records and actual next heap before any header field is decoded. -/
theorem list_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (before : pointer.toNat+length.toNat≤heap.toNat)
    (sizeBound : 16*length.toNat<2^64)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ header payload : BitVec 64,∃ topPost : PanSemStateFiniteExact 64 Guest.HostMemory,∃ sliced : PanSemStateFiniteExact 64 Guest.HostMemory,∃ items : List Rlp.ListItem,∃ count : BitVec 64,∃ inner,
      Rlp.CurrentDecode.Complete pointer length (Rlp.Item.result pointer header payload 1#64) ∧
      Rlp.ListItems sliced (pointer+header) payload.toNat items ∧ count.toNat=items.length ∧ count.toNat≤payload.toNat ∧
      Rlp.Slices.Records sliced.memory heap (pointer+header) items ∧ heap.toNat+16*count.toNat≤2952790016 ∧
      CurrentStartup.ArenaState sliced ∧ sliced.memaddrs=source.memaddrs ∧ sliced.be=source.be ∧
      sliced.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (count*16#64)))) ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat→sliced.memory query=source.memory query) ∧
      sliced.clock≤source.clock ∧ source.clock-sliced.clock≤131*length.toNat+17 ∧
      let topState:=setVarHOLFinite (ofString "top") (Rlp.Item.result pointer header payload 1#64) {topPost with locals:=source.locals}
      evaluateHOLFiniteState (CallNormal.continuationEntry topState sliced "lst" (Rlp.Slices.result heap count)) afterList=(some (.returned value),inner) ∧
      post=restore source "top" (restore topState "lst" inner) := by
  have fits : pointer.toNat+length.toNat<2^64 := by have h:=heap.isLt; omega
  obtain ⟨header,payload,topPost,middle,complete,forward,price,topFrame,remaining,endpoint⟩:=top_kind_returned source post pointer length pointerCell lengthCell arena fits value run
  let topState:=setVarHOLFinite (ofString "top") (Rlp.Item.result pointer header payload 1#64) {topPost with locals:=source.locals}
  have topGlobals := congrArg PanSemStateFiniteExact.globals topFrame.metadata
  change topPost.globals=source.globals at topGlobals
  have topHeap : topState.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) := by
    change topPost.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
    rw [topGlobals]
    exact heapGlobal
  have topCell : topState.locals.lookup (ofString "top")=some (Rlp.Item.result pointer header payload 1#64) := by
    simp [topState,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have extents:=complete
  obtain ⟨actualHeader,actualPayload,actualFlag,same,small,positive,extent,binary,listHead⟩:=extents
  have words : (1#64 : BitVec 64)=actualFlag ∧ header=actualHeader ∧ payload=actualPayload ∧ header+payload=actualHeader+actualPayload := by
    simpa [Rlp.Item.result] using same
  have headerEq:=words.2.1.symm
  have payloadEq:=words.2.2.1.symm
  have flagEq:=words.1.symm
  subst actualHeader actualPayload actualFlag
  have number : (pointer+header).toNat=pointer.toNat+header.toNat := BitVec.toNat_add_of_lt (by omega)
  have args : evalListHOLFinite topState (h:=fun query=>Classical.propDecidable (topState.memaddrs query)) listArguments=some (Rlp.Header.values (pointer+header) payload) := by
    simp [listArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,topCell,Rlp.Item.result]
  rw [after_top_shape.2] at remaining
  obtain ⟨funded,sliced,items,count,inner,model,countEq,countBound,records,room,nextArena,domain,endian,globals,frame,metadata,above,actualForward,slicePrice,continued,restored⟩:=
    Rlp.CurrentSlices.scoped_normal topState middle (pointer+header) payload heap ((Rlp.LiveArena.of_startup arena).of_metadata topFrame.metadata) topHeap heapBound (by rw [number]; omega) (by omega) "lst" listArguments afterList args value remaining
  change sliced.clock≤topPost.clock at actualForward
  have sourceDomain : sliced.memaddrs=source.memaddrs := domain.trans (MemoryMetadata.domain topFrame.metadata)
  have sourceEndian : sliced.be=source.be := endian.trans (MemoryMetadata.endian topFrame.metadata)
  have sourceGlobals : sliced.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (count*16#64)))) :=
    globals.trans (congrArg (fun stateGlobals : HolFiniteMapExact MlS (ValueHOL 64)=>stateGlobals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (count*16#64))))) topGlobals)
  have sourceMemory : ∀ query : BitVec 64,query.toNat<heap.toNat→sliced.memory query=source.memory query := by
    intro query earlier
    exact (frame query earlier).trans (topFrame.outside query (Or.inl (Nat.lt_of_lt_of_le earlier heapBound)))
  refine ⟨header,payload,topPost,sliced,items,count,inner,complete,model,countEq,countBound,records,room,Rlp.CurrentSlices.startup_of_heap arena nextArena _ sourceGlobals,sourceDomain,sourceEndian,sourceGlobals,sourceMemory,?_,?_,continued,?_⟩
  · omega
  · change topPost.clock-sliced.clock≤71*payload.toNat+4 at slicePrice
    omega
  · rw [endpoint,restored]

end InitECandidate.Solver.Headers.CurrentDecode

#print axioms InitECandidate.Solver.Headers.CurrentDecode.list_returned
