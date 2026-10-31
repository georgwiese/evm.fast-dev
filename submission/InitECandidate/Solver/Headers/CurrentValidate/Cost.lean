import InitECandidate.Solver.Headers.CurrentValidate.Loops
import InitECandidate.Solver.Headers.CurrentValidate.InitialState

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix

/-- Complete actual validate_headers212, including count rejection, both
allocator failures and every loop exit. Only current real input/record and
workspace geometry is supplied; later room and states come from execution. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper : Nat)
    (arena : CurrentStartup.ArenaState source) (environment : CurrentKeccak.Hash.Environment source stp pad)
    (rows : Rows source array pointers lengths count.toNat lower upper)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (before : upper≤heap.toNat) (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (aligned : lower%8=0) (inputLower : 2701131776≤lower)
    (lengthLimits : ∀ index<count.toNat,(lengths index).toNat≤1024) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤66208386 := by
  let post:=(evaluateHOLFiniteState source body).2
  let result:=(evaluateHOLFiniteState source body).1
  have run : evaluateHOLFiniteState source body=(result,post) := rfl
  change source.clock-post.clock≤_
  rcases entry_trace source post heap count countCell heapCell heapBound arena.code result run with stopped|reached
  · omega
  · obtain ⟨small,funded,firstRoom,secondRoom,inner,continued,endpoint⟩:=reached
    have geometry:=geometry_of_room heap count small heapLower heapAligned firstRoom secondRoom
    obtain ⟨layout,state⟩:=initial_round source source array heap count stp pad pointers lengths lower upper arena environment
      (HashInput.Frame.refl source lower upper) rows geometry arrayCell countCell before small stateBefore padBefore aligned inputLower lengthLimits (HeapGlobals.refl source)
    let data:=invocationData array heap count stp pad pointers lengths lower upper
    let entry:=loopEntry source heap count
    have loopCost:=loops_cost data source entry state layout
    rw [continued] at loopCost
    have loopForward:=evaluateHOLFiniteState_clock_le entry loops
    rw [continued] at loopForward
    have entryClock:=loopEntry_clock source heap count
    have finalClock : post.clock=inner.clock := by rw [endpoint]; rfl
    change entry.clock-inner.clock≤258497*count.toNat+130*(count.toNat-1) at loopCost
    change inner.clock≤entry.clock at loopForward
    change entry.clock=source.clock-2 at entryClock
    rw [finalClock]
    omega

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.body_cost
