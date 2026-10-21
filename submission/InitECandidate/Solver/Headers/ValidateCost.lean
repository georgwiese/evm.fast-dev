import InitECandidate.Solver.Headers.ValidateLinkSuffix
import InitECandidate.Solver.Headers.ValidateInitialRound

namespace InitECandidate.Solver.Headers.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Complete unchanged validate_headers214 on every outcome, including
count/allocation/read/comparison failures. The byte budget is shared by
the actual decoded rows, and real allocation room is derived from the run.
This is a source call/loop allowance; target straight-line work is separate. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count cursor limit stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper budget : Nat)
    (installed : Input.OriginalCode.Installed source.code)
    (shape : source.eshapes.lookup (ofString "HdrErr")=some .one)
    (arena : Rlp.Validation.Arena source cursor limit) (environment : Keccak256.Environment source stp pad)
    (rows : Rows source array pointers lengths count.toNat lower upper)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0)
    (before : upper≤heap.toNat)
    (stateArena : AllocatedBytes.Arena stp 200) (stateAligned : stp.toNat%8=0)
    (padArena : AllocatedBytes.Arena pad 136) (padAligned : pad.toNat%8=0)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (aligned : lower%8=0) (inputLower : 2701131776≤lower) (scratchBefore : cursor.toNat≤lower)
    (byteBudget : Input.VarList.sumPrefix (fun index=>(lengths index).toNat) count.toNat≤budget) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤
      251*budget+1578*count.toNat+20*(budget/136)+130*(count.toNat-1)+4 := by
  let post:=(evaluateHOLFiniteState source body).2
  let result:=(evaluateHOLFiniteState source body).1
  have run : evaluateHOLFiniteState source body=(result,post) := rfl
  change source.clock-post.clock≤_
  rcases entry_trace source post heap count countCell heapCell heapBound installed result run with stopped|reached
  · omega
  · obtain ⟨small,funded,firstRoom,secondRoom,inner,continued,endpoint⟩ := reached
    have geometry:=geometry_of_room heap count small heapLower heapAligned firstRoom secondRoom
    obtain ⟨layout,state⟩ := initial_round source source array heap count cursor limit stp pad pointers lengths lower upper installed shape arena environment
      (Input.HashInput.Frame.refl source lower upper) rows geometry arrayCell countCell before small stateArena stateAligned padArena padAligned stateBefore padBefore aligned inputLower scratchBefore
    let data:=invocationData array heap count cursor limit stp pad pointers lengths lower upper
    let entry:=loopEntry source heap count
    have loopCost:=loops_cost data source entry state layout
    rw [continued] at loopCost
    have loopForward:=evaluateHOLFiniteState_clock_le entry loops
    rw [continued] at loopForward
    have collected:=decode_sum_bound data budget byteBudget
    have entryClock:=loopEntry_clock source heap count
    have finalClock : post.clock=inner.clock := by rw [endpoint]; rfl
    change entry.clock-inner.clock≤decodeSum data data.count+130*(data.count-1) at loopCost
    change inner.clock≤entry.clock at loopForward
    change entry.clock=source.clock-2 at entryClock
    change decodeSum data data.count≤251*budget+1578*count.toNat+20*(budget/136) at collected
    change entry.clock-inner.clock≤decodeSum data data.count+130*(count.toNat-1) at loopCost
    rw [finalClock]
    omega

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.body_cost
