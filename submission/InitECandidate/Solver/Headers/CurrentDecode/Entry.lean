import InitECandidate.Solver.Headers.CurrentDecode.List
import InitECandidate.Solver.Headers.CurrentDecode.AllocationReturned

namespace InitECandidate.Solver.Headers.CurrentDecode
open Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- Reach the actual field pipeline only after real parsing, the21/23 guard
and a normally returning248-byte allocation have supplied all their data. -/
theorem field_entry_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (before : pointer.toNat+length.toNat≤heap.toNat)
    (sizeBound : 16*length.toNat<2^64)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ header payload : BitVec 64,∃ clock : Nat,∃ sliced : PanSemStateFiniteExact 64 Guest.HostMemory,∃ items : List Rlp.ListItem,∃ count : BitVec 64,∃ final,
      Rlp.CurrentDecode.Complete pointer length (Rlp.Item.result pointer header payload 1#64) ∧
      Rlp.ListItems sliced (pointer+header) payload.toNat items ∧ count.toNat=items.length ∧
      Rlp.Slices.Records sliced.memory heap (pointer+header) items ∧ heap.toNat+16*count.toNat≤2952790016 ∧
      CurrentStartup.ArenaState sliced ∧ (count=21#64 ∨ count=23#64) ∧ 1≤sliced.clock ∧
      (PersistentAlloc.rounded heap (count*16#64)).toNat+248≤2952790016 ∧
      let topState:=setVarHOLFinite (ofString "top") (Rlp.Item.result pointer header payload 1#64) {source with clock:=clock}
      let listState:=CallNormal.continuationEntry topState sliced "lst" (Rlp.Slices.result heap count)
      let reached:=allocationEntry listState heap count (PersistentAlloc.rounded heap (count*16#64))
      reached.clock≤source.clock ∧ source.clock-reached.clock≤103*length.toNat+18 ∧
      reached.memory=sliced.memory ∧
      evaluateHOLFiniteState reached afterAllocation=(some (.returned value),final) ∧
      post=restore source "top" (restore topState "lst"
        (restoreDeclared listState heap count (restore (counted (declared listState heap count) count) "h" final))) := by
  obtain ⟨header,payload,clock,sliced,items,count,inner,complete,model,countEq,countBound,records,room,nextArena,domain,endian,globals,frame,forward,price,remaining,endpoint⟩:=
    list_returned source post pointer length heap pointerCell lengthCell arena heapGlobal heapBound before sizeBound value run
  let topState:=setVarHOLFinite (ofString "top") (Rlp.Item.result pointer header payload 1#64) {source with clock:=clock}
  let listState:=CallNormal.continuationEntry topState sliced "lst" (Rlp.Slices.result heap count)
  have listCell : listState.locals.lookup (ofString "lst")=some (Rlp.Slices.result heap count) := by
    simp [listState,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have product : (count*16#64).toNat=16*count.toNat := by
    rw [BitVec.toNat_mul,Nat.mod_eq_of_lt (by change count.toNat*16<2^64; omega)]
    change count.toNat*16=16*count.toNat
    omega
  have allocationRoom : heap.toNat+(count*16#64).toNat≤2952790016 := by rw [product]; exact room
  have guards:=PersistentAlloc.guards heap (count*16#64) allocationRoom
  have allocatedBound : (PersistentAlloc.rounded heap (count*16#64)).toNat≤2952790016 := guards.2.2.2.1
  have listHeap : listState.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (count*16#64)))) := by
    change sliced.globals.lookup _=_
    rw [globals]
    simp [HolFiniteMapExact.update,FUPDATE]
  obtain ⟨countValid,funded,headerRoom,final,continued,restored⟩:=allocation_returned listState inner heap count (PersistentAlloc.rounded heap (count*16#64)) listCell listHeap allocatedBound nextArena.code value remaining
  change 1≤sliced.clock at funded
  obtain ⟨_,_,_,_,_,memory,reachedClock⟩:=allocation_fields listState heap count (PersistentAlloc.rounded heap (count*16#64))
  change (allocationEntry listState heap count (PersistentAlloc.rounded heap (count*16#64))).clock=sliced.clock-1 at reachedClock
  refine ⟨header,payload,clock,sliced,items,count,final,complete,model,countEq,records,room,nextArena,countValid,funded,headerRoom,?_,?_,memory,continued,?_⟩
  · rw [reachedClock]; omega
  · rw [reachedClock]; omega
  · rw [endpoint,restored]

end InitECandidate.Solver.Headers.CurrentDecode

#print axioms InitECandidate.Solver.Headers.CurrentDecode.field_entry_returned
