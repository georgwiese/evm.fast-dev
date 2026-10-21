import InitECandidate.Solver.Headers.DecodeAllocationTrace
import InitECandidate.Solver.Headers.DecodeFrame

namespace InitECandidate.Solver.Headers.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def fieldEntry (source parsed sliced : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload heap count : BitVec 64) :=
  allocationEntry (listState source parsed sliced pointer header payload heap count) heap count (PersistentAlloc.rounded heap (count*16#64))

def restoreFieldEntry (source parsed sliced : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload heap count : BitVec 64) (target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  let listSource:=listState source parsed sliced pointer header payload heap count
  restore source "top" (restore (topState source parsed pointer header payload) "lst"
    (restoreDeclared listSource heap count (restore (counted (declared listSource heap count) count) "h" target)))

/-- Actual original header execution through both complete RLP passes,
21/23 count dispatch and248-byte header allocation. All early outcomes are
charged; the reached field pipeline carries genuine decoded data and exact
outer lexical restoration. This is a source-prefix bound, not target K. -/
theorem field_entry_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit : BitVec 64) (cutoff : Nat)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (shape : source.eshapes.lookup (ofString "HdrErr")=some .one)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) :
    source.clock-post.clock≤131*length.toNat+81 ∨
      ∃ parsed header payload sliced items count final,
        Rlp.Decode.Returned source parsed pointer length cursor limit (Rlp.Item.result pointer header payload 1#64) ∧
        Rlp.Slices.Returned (topState source parsed pointer header payload) sliced (pointer+header) payload heap cursor limit count items ∧
        (count=21#64 ∨ count=23#64) ∧ 1≤sliced.clock ∧
        (PersistentAlloc.rounded heap (count*16#64)).toNat+248≤33806089496 ∧
        (fieldEntry source parsed sliced pointer header payload heap count).clock≤source.clock ∧
        source.clock-(fieldEntry source parsed sliced pointer header payload heap count).clock≤131*length.toNat+81 ∧
        evaluateHOLFiniteState (fieldEntry source parsed sliced pointer header payload heap count) afterAllocation=(result,final) ∧
        post=restoreFieldEntry source parsed sliced pointer header payload heap count final := by
  rcases slices_trace source post pointer length heap cursor limit cutoff pointerCell lengthCell arena heapGlobal heapBound before sizeBound aligned scratchBelow inputAbove installed shape result run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨parsed,header,payload,sliced,items,count,inner,topReturned,slicesReturned,forward,price,remaining,endpoint⟩ := reached
    let listSource:=listState source parsed sliced pointer header payload heap count
    have listCell : listSource.locals.lookup (ofString "lst")=some (Rlp.Slices.result heap count) := by
      simp [listSource,listState,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    have product : (count*16#64).toNat=16*count.toNat := by
      rw [BitVec.toNat_mul,Nat.mod_eq_of_lt (by have h:=slicesReturned.room; change count.toNat*16<2^64; omega)]
      change count.toNat*16=16*count.toNat
      omega
    have room : heap.toNat+(count*16#64).toNat≤33806089496 := by rw [product]; exact slicesReturned.room
    have guards:=PersistentAlloc.guards heap (count*16#64) room
    have allocatedBound : (PersistentAlloc.rounded heap (count*16#64)).toNat≤33806089496 := guards.2.2.2.1
    have listHeap : listSource.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (count*16#64)))) := slicesReturned.heapGlobal
    have code : sliced.code=source.code := slicesReturned.code.trans topReturned.code
    have listInstalled : Input.OriginalCode.Installed listSource.code := by change Input.OriginalCode.Installed sliced.code; rw [code]; exact installed
    have exceptions : sliced.eshapes=source.eshapes := slicesReturned.exceptions.trans topReturned.exceptions
    have listShape : listSource.eshapes.lookup (ofString "HdrErr")=some .one := by change sliced.eshapes.lookup _=_; rw [exceptions]; exact shape
    rcases allocation_trace listSource inner heap count (PersistentAlloc.rounded heap (count*16#64)) listCell listHeap allocatedBound listInstalled listShape result remaining with stopped|allocated
    · have back:=evaluateHOLFiniteState_clock_le listSource afterList
      rw [remaining] at back
      change inner.clock≤sliced.clock at back
      change sliced.clock-inner.clock≤2 at stopped
      have finalClock : post.clock=inner.clock := by rw [endpoint]; rfl
      exact Or.inl (by omega)
    · obtain ⟨countValid,funded,headerRoom,final,continued,restored⟩ := allocated
      change 1≤sliced.clock at funded
      obtain ⟨_,_,_,_,_,_,clock⟩ := allocation_fields listSource heap count (PersistentAlloc.rounded heap (count*16#64))
      change (fieldEntry source parsed sliced pointer header payload heap count).clock=sliced.clock-1 at clock
      have entryForward : (fieldEntry source parsed sliced pointer header payload heap count).clock≤source.clock := by omega
      have entryPrice : source.clock-(fieldEntry source parsed sliced pointer header payload heap count).clock≤131*length.toNat+81 := by omega
      exact Or.inr ⟨parsed,header,payload,sliced,items,count,final,topReturned,slicesReturned,countValid,funded,headerRoom,entryForward,entryPrice,continued,
        by rw [endpoint,restored]; rfl⟩

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.field_entry_trace
