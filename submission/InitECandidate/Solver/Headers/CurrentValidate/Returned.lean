import InitECandidate.Solver.Headers.CurrentValidate.EntryReturned
import InitECandidate.Solver.Headers.CurrentValidate.LoopReturned
import InitECandidate.Solver.Headers.CurrentValidate.InitialState

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix

/-- A genuine current whole-validator return derives both actual arrays,
real count/allocator geometry and its final physical loop state. Lexical
exits erase only locals and clock, so every memory/global fact is retained. -/
theorem body_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper : Nat)
    (arena : CurrentStartup.ArenaState source) (environment : CurrentKeccak.Hash.Environment source stp pad)
    (rows : Rows source array pointers lengths count.toNat lower upper)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (before : upper≤heap.toNat) (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (aligned : lower%8=0) (inputLower : 2701131776≤lower)
    (lengthLimits : ∀ index<count.toNat,(lengths index).toNat≤1024)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=result heap (hashesPointer heap count) ∧ count.toNat≤256 ∧ Geometry heap count ∧
      ∃ finish index,index≤count.toNat+1 ∧
        RoundState (invocationData array heap count stp pad pointers lengths lower upper) source finish index ∧
        LocalEffects.erase post=LocalEffects.erase finish := by
  obtain ⟨small,funded,firstRoom,secondRoom,inner,continued,endpoint⟩:=entry_returned source post heap count countCell heapCell heapBound arena.code value run
  have geometry:=geometry_of_room heap count small heapLower heapAligned firstRoom secondRoom
  obtain ⟨layout,state⟩:=initial_round source source array heap count stp pad pointers lengths lower upper arena environment
    (HashInput.Frame.refl source lower upper) rows geometry arrayCell countCell before small stateBefore padBefore aligned inputLower lengthLimits (HeapGlobals.refl source)
  obtain ⟨answer,finish,index,bounded,finalState,restored⟩:=loops_returned (invocationData array heap count stp pad pointers lengths lower upper) source (loopEntry source heap count) inner state layout value continued
  exact ⟨answer,small,geometry,finish,index,bounded,finalState,by rw [endpoint,restored]; rfl⟩

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.body_returned
