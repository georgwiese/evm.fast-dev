import InitECandidate.Solver.Headers.PipelineCost
import InitECandidate.Solver.Headers.PipelinePrice
import InitECandidate.Solver.Headers.DecodeInitialState

namespace InitECandidate.Solver.Headers.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Complete unchanged decode_header210, including both real RLP passes,
count checks, actual allocation, every field and both21/23 tails. All
outcomes are bounded; no helper success or future header image is assumed.
This counts source call/loop ticks, not straight-line target instructions. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit : BitVec 64) (cutoff : Nat)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (inputLower : 2701131776≤pointer.toNat) (heapAligned : heap.toNat%8=0)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (shape : source.eshapes.lookup (ofString "HdrErr")=some .one) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤251*length.toNat+1373 := by
  let result:=(evaluateHOLFiniteState source body).1
  let post:=(evaluateHOLFiniteState source body).2
  have run : evaluateHOLFiniteState source body=(result,post) := rfl
  change source.clock-post.clock≤_
  rcases field_entry_trace source post pointer length heap cursor limit cutoff pointerCell lengthCell arena heapGlobal heapBound before sizeBound aligned scratchBelow inputAbove installed shape result run with stopped|reached
  · omega
  · obtain ⟨parsed,header,payload,sliced,items,count,final,topReturned,slicesReturned,countValid,funded,headerRoom,entryForward,entryPrice,continued,postEq⟩ := reached
    have state:=initial_field_state source parsed sliced pointer length header payload heap cursor limit count items cutoff topReturned slicesReturned countValid headerRoom installed inputLower heapAligned before aligned scratchBelow inputAbove
    let entry:=fieldEntry source parsed sliced pointer header payload heap count
    let current:=if count=23#64 then 1#64 else 0#64
    have countBound : items.length≤23 := by rcases state.branch with ⟨_,size⟩|⟨_,size⟩ <;> omega
    have fieldsPrice:=Pipeline.cost entry (pointer+header) heap (PersistentAlloc.rounded heap (count*16#64)) cursor limit current payload.toNat cutoff items [] Pipeline.fields state (Pipeline.fields_valid current items.length state.branch)
    rw [←Pipeline.original_fields,continued] at fieldsPrice
    have rowPrice:=Pipeline.price_bytes entry (pointer+header) payload.toNat items current state.slices.itemsAtInput countBound
    have extent:=(Rlp.Decode.Complete.fields pointer length header payload 1#64 topReturned.complete).2.2.1
    have finalForward:=evaluateHOLFiniteState_clock_le entry afterAllocation
    rw [continued] at finalForward
    have finalClock : post.clock=final.clock := by rw [postEq]; rfl
    change entry.clock-final.clock≤_ at fieldsPrice
    change final.clock≤entry.clock at finalForward
    change entry.clock≤source.clock at entryForward
    change source.clock-entry.clock≤_ at entryPrice
    rw [finalClock]
    omega

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.body_cost
