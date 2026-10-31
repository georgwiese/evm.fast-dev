import InitECandidate.Solver.Headers.CurrentDecode.InitialState
import InitECandidate.Solver.Headers.CurrentPipeline.FieldsCost

namespace InitECandidate.Solver.Headers.CurrentDecode
open Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix

/-- All actual outcomes after slice conversion, including count rejection,
failed allocation and the complete reached field pipeline. Room comes only
from the same real allocator return; exception metadata is unrestricted. -/
theorem after_list_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header count : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem)
    (data : CurrentHelpers.SliceImage source pointer array bytes items)
    (countEq : count.toNat=items.length)
    (listCell : source.locals.lookup (ofString "lst")=some (Rlp.Slices.result array count))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word header)))
    (bounded : header.toNat≤2952790016) (before : array.toNat+16*items.length≤header.toNat)
    (aligned : header.toNat%8=0) :
    source.clock-(evaluateHOLFiniteState source afterList).2.clock≤120*bytes+456 := by
  obtain ⟨result,post,run⟩ : ∃ result post,evaluateHOLFiniteState source afterList=(result,post) := ⟨_,_,rfl⟩
  rw [run]
  change source.clock-post.clock≤120*bytes+456
  rcases allocation_trace source post array count header listCell heap bounded data.arena.code result run with stopped|reached
  · omega
  · obtain ⟨countValid,funded,room,inner,continued,endpoint⟩:=reached
    let ready:=allocationEntry source array count header
    have state:=allocation_state source pointer array header count bytes items data countEq countValid before room aligned
    have price:=CurrentPipeline.fields_cost ready pointer array header (if count=23#64 then 1#64 else 0#64) bytes items state
    rw [continued] at price
    have forward:=evaluateHOLFiniteState_clock_le ready afterAllocation
    rw [continued] at forward
    obtain ⟨_,_,_,_,_,_,clock⟩:=allocation_fields source array count header
    change ready.clock=source.clock-1 at clock
    have finalClock : post.clock=inner.clock := by rw [endpoint]; rfl
    change ready.clock-inner.clock≤120*bytes+455 at price
    change inner.clock≤ready.clock at forward
    change source.clock-post.clock≤120*bytes+456
    rw [finalClock]
    omega

end InitECandidate.Solver.Headers.CurrentDecode

#print axioms InitECandidate.Solver.Headers.CurrentDecode.after_list_cost
