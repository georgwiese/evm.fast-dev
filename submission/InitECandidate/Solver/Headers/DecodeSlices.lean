import InitECandidate.Solver.Rlp.ItemCallEncoding
import InitECandidate.Solver.Headers.DecodePrefix
import InitECandidate.Solver.Rlp.SlicesTrace
import InitECandidate.Solver.Input.ClockCostSpendChain

namespace InitECandidate.Solver.Headers.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def topState (source parsed : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer header payload : BitVec 64) :=
  Input.CallNormal.continuationEntry source parsed "top" (Rlp.Item.result pointer header payload 1#64)

def listState (source parsed sliced : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload heap count : BitVec 64) :=
  Input.CallNormal.continuationEntry (topState source parsed pointer header payload) sliced "lst" (Rlp.Slices.result heap count)

/-- The original header decoder's complete RLP and slice-conversion prefix,
including every early outcome. Successful conversion supplies real record
cells and reached memory; both lexical scopes are retained exactly. -/
theorem slices_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit : BitVec 64) (cutoff : Nat)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat)
    (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (shape : source.eshapes.lookup (ofString "HdrErr")=some .one)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) :
    source.clock-post.clock≤131*length.toNat+79 ∨
      ∃ parsed header payload sliced items count inner,
        Rlp.Decode.Returned source parsed pointer length cursor limit (Rlp.Item.result pointer header payload 1#64) ∧
        Rlp.Slices.Returned (topState source parsed pointer header payload) sliced (pointer+header) payload heap cursor limit count items ∧
        sliced.clock≤source.clock ∧ source.clock-sliced.clock≤131*length.toNat+79 ∧
        evaluateHOLFiniteState (listState source parsed sliced pointer header payload heap count) afterList=(result,inner) ∧
        post=restore source "top" (restore (topState source parsed pointer header payload) "lst" inner) := by
  have fits : pointer.toNat+length.toNat<2^64 := by have := heap.isLt; omega
  rcases top_kind_trace source post pointer length cursor limit pointerCell lengthCell arena fits installed shape result run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨parsed,header,payload,inner,topReturned,remaining,endpoint⟩ := reached
    have totalExtent : header.toNat+payload.toNat=length.toNat := by
      obtain ⟨h,p,f,same,small,positive,extent,binary,listHeader⟩ := topReturned.complete
      have parts := Rlp.Item.result_injective pointer header payload 1#64 h p f same
      rw [parts.1,parts.2.1]
      exact extent
    have pointerNumber : (pointer+header).toNat=pointer.toNat+header.toNat := BitVec.toNat_add_of_lt (by omega)
    let ready := topState source parsed pointer header payload
    have topCell : ready.locals.lookup (ofString "top")=some (Rlp.Item.result pointer header payload 1#64) := by
      simp [ready,topState,Input.CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    have args : evalListHOLFinite ready (h:=fun query=>Classical.propDecidable (ready.memaddrs query)) listArguments=some (Rlp.Header.values (pointer+header) payload) := by
      simp [listArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,topCell,Rlp.Item.result]
    have readyArena := Rlp.Validation.Arena.of_fields parsed ready cursor limit topReturned.arena rfl rfl
    have readyHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) := (topReturned.globals _).trans heapGlobal
    have readyCode : Input.OriginalCode.Installed ready.code := by change Input.OriginalCode.Installed parsed.code; rw [topReturned.code]; exact installed
    change evaluateHOLFiniteState ready afterKind=(result,inner) at remaining
    rw [after_top_shape.2] at remaining
    rcases Rlp.Slices.scoped_trace ready inner (pointer+header) payload heap cursor limit cutoff "lst" listArguments afterList args readyArena readyHeap heapBound
        (by rw [pointerNumber]; omega) (by omega) aligned scratchBelow (by rw [pointerNumber]; omega) readyCode result remaining with stopped|reached
    · have back := evaluateHOLFiniteState_clock_le ready afterKind
      have originalRun : evaluateHOLFiniteState ready afterKind=(result,inner) := by rw [after_top_shape.2]; exact remaining
      rw [originalRun] at back
      change inner.clock≤parsed.clock at back
      change parsed.clock-inner.clock≤71*payload.toNat+35 at stopped
      have finalClock : post.clock=inner.clock := by rw [endpoint]; rfl
      have firstCost := topReturned.cost
      have forward := topReturned.forward
      exact Or.inl (by omega)
    · obtain ⟨sliced,items,count,final,slicesReturned,continued,restored⟩ := reached
      have forward : sliced.clock≤source.clock := slicesReturned.forward.trans topReturned.forward
      have firstCost := topReturned.cost
      have nextCost := slicesReturned.cost
      change parsed.clock-sliced.clock≤71*payload.toNat+35 at nextCost
      have nextForward : sliced.clock≤parsed.clock := slicesReturned.forward
      have cost : source.clock-sliced.clock≤131*length.toNat+79 := by have h:=topReturned.forward; omega
      exact Or.inr ⟨parsed,header,payload,sliced,items,count,final,topReturned,slicesReturned,forward,cost,continued,by rw [endpoint,restored]⟩

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.slices_trace
