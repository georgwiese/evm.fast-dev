import InitECandidate.Solver.Headers.CurrentDecode.List
import InitECandidate.Solver.Headers.CurrentDecode.AllocationReturned
import InitECandidate.Solver.Headers.CurrentDecode.InitialState
import InitECandidate.Solver.Headers.CurrentPipeline.Memory

namespace InitECandidate.Solver.Headers.CurrentDecode
open Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 10000 in
/-- Every successful unchanged header decoder returns its actual fresh
248-byte header. Earlier memory and every global except the advancing heap
are preserved, so later witness iterations can reuse their original data. -/
theorem normal_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (before : pointer.toNat+length.toNat≤heap.toNat)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ record : BitVec 64,value=.val (.word record) ∧ heap.toNat≤record.toNat ∧
      record.toNat+248≤2952790016 ∧ record.toNat%8=0 ∧
      CurrentStartup.ArenaState post ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded record 248#64))) ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → post.memory query=source.memory query) ∧
      (∀ key,key≠ofString "heap_ptr" → post.globals.lookup key=source.globals.lookup key) ∧
      post.memaddrs=source.memaddrs ∧ post.be=source.be ∧
      (PersistentAlloc.rounded record 248#64).toNat≤heap.toNat+616 := by
  have sizeBound : 16*length.toNat<2^64 := by omega
  obtain ⟨header,payload,topPost,sliced,items,count,inner,complete,model,countEq,countBound,records,room,nextArena,domain,endian,globals,frame,forward,price,remaining,endpoint⟩:=
    list_returned source post pointer length heap pointerCell lengthCell arena heapGlobal heapBound before sizeBound value run
  let topState:=setVarHOLFinite (ofString "top") (Rlp.Item.result pointer header payload 1#64) {topPost with locals:=source.locals}
  let listState:=CallNormal.continuationEntry topState sliced "lst" (Rlp.Slices.result heap count)
  let record:=PersistentAlloc.rounded heap (count*16#64)
  have listCell : listState.locals.lookup (ofString "lst")=some (Rlp.Slices.result heap count) := by
    simp [listState,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have product : (count*16#64).toNat=16*count.toNat := by
    rw [BitVec.toNat_mul,Nat.mod_eq_of_lt (by change count.toNat*16<2^64; omega)]
    change count.toNat*16=16*count.toNat
    omega
  have allocationRoom : heap.toNat+(count*16#64).toNat≤2952790016 := by rw [product]; exact room
  have guards:=PersistentAlloc.guards heap (count*16#64) allocationRoom
  have listHeap : listState.globals.lookup (ofString "heap_ptr")=some (.val (.word record)) := by
    change sliced.globals.lookup _=_
    rw [globals]
    simp [record,HolFiniteMapExact.update,FUPDATE]
  obtain ⟨countValid,funded,headerRoom,final,continued,restored⟩:=allocation_returned listState inner heap count record listCell listHeap guards.2.2.2.1 nextArena.code value remaining
  have fits : pointer.toNat+length.toNat<2^64 := by have h:=heap.isLt; omega
  obtain ⟨actualHeader,actualPayload,actualFlag,same,small,positive,extent,binary,listHead⟩:=complete
  have words : (1#64 : BitVec 64)=actualFlag ∧ header=actualHeader ∧ payload=actualPayload ∧ header+payload=actualHeader+actualPayload := by
    simpa [Rlp.Item.result] using same
  have headerEq:=words.2.1.symm
  have payloadEq:=words.2.2.1.symm
  have flagEq:=words.1.symm
  subst actualHeader actualPayload actualFlag
  have payloadAddress : (pointer+header).toNat=pointer.toNat+header.toNat := BitVec.toNat_add_of_lt (by omega)
  have payloadBefore : (pointer+header).toNat+payload.toNat≤heap.toNat := by rw [payloadAddress]; omega
  have image : CurrentHelpers.SliceImage sliced (pointer+header) heap payload.toNat items :=
    ⟨model,records,nextArena,⟨heapLower,by omega⟩,heapAligned,(by have h:=heap.isLt; omega),payloadBefore⟩
  have listImage : CurrentHelpers.SliceImage listState (pointer+header) heap payload.toNat items := image.of_frame rfl
  have recordsBefore : heap.toNat+16*items.length≤record.toNat := by
    rw [←countEq,←product]
    exact guards.2.2.1
  let reached:=allocationEntry listState heap count record
  let current : BitVec 64:=if count=23#64 then 1#64 else 0#64
  have state : CurrentPipeline.State reached (pointer+header) heap record current payload.toNat items [] :=
    allocation_state listState (pointer+header) heap record count payload.toNat items listImage countEq countValid recordsBefore headerRoom guards.2.2.2.2
  rw [Pipeline.original_fields] at continued
  have valid:=Pipeline.fields_valid current items.length state.branch
  obtain ⟨valueEq,finish,finalActive,finishState,erased⟩:=CurrentPipeline.returned_state reached final (pointer+header) heap record current payload.toNat items [] _ state valid value continued
  have fieldsFrame:=CurrentPipeline.normal_frame_data reached final (pointer+header) heap record current payload.toNat items [] _ state valid _ (Or.inr ⟨value,rfl⟩) continued
  have postFrame : LocalEffects.erase post=LocalEffects.erase final := by rw [endpoint,restored]; rfl
  have actualArena : CurrentStartup.ArenaState post := finishState.slices.arena.of_frame (postFrame.trans erased)
  have finalGlobals : post.globals=final.globals := by
    have projected:=congrArg PanSemStateFiniteExact.globals postFrame
    exact projected
  have reachedGlobals : ∀ key,post.globals.lookup key=reached.globals.lookup key := by
    intro key
    rw [finalGlobals]
    exact fieldsFrame.globals key
  have postHeap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded record 248#64))) := by
    rw [reachedGlobals]
    exact state.heap
  have postMemory : ∀ query : BitVec 64,query.toNat<heap.toNat → post.memory query=source.memory query := by
    intro query lower
    rw [congrFun (LocalEffects.memory_of_erase final post postFrame) query]
    have earlier : query.toNat<record.toNat := by omega
    rw [fieldsFrame.memory query earlier]
    have reachedMemory:=(allocation_fields listState heap count record).2.2.2.2.2.1
    change reached.memory=listState.memory at reachedMemory
    rw [reachedMemory]
    exact frame query lower
  have otherGlobals : ∀ key,key≠ofString "heap_ptr" → post.globals.lookup key=source.globals.lookup key := by
    intro key different
    rw [reachedGlobals]
    change ((counted (declared listState heap count) count).globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded record 248#64)))).lookup key=_
    have baseFrame:=(counted_frame listState heap count).1
    have baseGlobals:=congrArg PanSemStateFiniteExact.globals baseFrame
    change (counted (declared listState heap count) count).globals=listState.globals at baseGlobals
    rw [baseGlobals]
    change (sliced.globals.update _).lookup key=_
    rw [globals]
    simp [HolFiniteMapExact.update,FUPDATE,different,Ne.symm different]
  have postDomain : post.memaddrs=source.memaddrs := by
    have actual:=congrArg PanSemStateFiniteExact.memaddrs (postFrame.trans erased)
    exact actual.trans (finishState.slices.arena.domain.trans arena.domain.symm)
  have postEndian : post.be=source.be := by
    have actual:=congrArg PanSemStateFiniteExact.be postFrame
    have base:=congrArg PanSemStateFiniteExact.be (counted_frame listState heap count).1
    change (counted (declared listState heap count) count).be=listState.be at base
    have readyEndian : reached.be=sliced.be := base
    exact actual.trans (fieldsFrame.endian.trans (readyEndian.trans endian))
  have firstSize : (count*16#64).toNat≤368 := by rcases countValid with rfl|rfl <;> decide
  have firstNumber:=PersistentAlloc.rounded_nat heap (count*16#64) (by omega)
  have recordBound : record.toNat≤heap.toNat+368 := by
    change (PersistentAlloc.rounded heap (count*16#64)).toNat≤_
    rw [firstNumber]
    omega
  have finalNumber:=PersistentAlloc.rounded_nat record 248#64 (by change record.toNat+248+7<2^64; omega)
  have growth : (PersistentAlloc.rounded record 248#64).toNat≤heap.toNat+616 := by
    rw [finalNumber]
    change (record.toNat+248+7)/8*8≤heap.toNat+616
    omega
  exact ⟨record,valueEq,(by omega),headerRoom,guards.2.2.2.2,actualArena,postHeap,postMemory,otherGlobals,postDomain,postEndian,growth⟩

end InitECandidate.Solver.Headers.CurrentDecode

#print axioms InitECandidate.Solver.Headers.CurrentDecode.normal_frame
