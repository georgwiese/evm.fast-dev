import InitECandidate.Solver.Headers.CurrentValidate.Round

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix

def invocationData (array heap count stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper : Nat) : Data := {
  array:=array,hs:=heap,hashes:=hashesPointer heap count,stp:=stp,pad:=pad,
  pointers:=pointers,lengths:=lengths,count:=count.toNat,lower:=lower,upper:=upper }

/-- Only the reached caller image and room derived from both real
allocations establish the first current validator loop state. -/
theorem initial_round (origin source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper : Nat)
    (arena : CurrentStartup.ArenaState source) (environment : CurrentKeccak.Hash.Environment source stp pad)
    (frame : HashInput.Frame origin source lower upper) (rows : Rows source array pointers lengths count.toNat lower upper)
    (geometry : Geometry heap count)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (before : upper≤heap.toNat) (small : count.toNat≤256)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (aligned : lower%8=0) (inputLower : 2701131776≤lower)
    (lengthLimits : ∀ index<count.toNat,(lengths index).toNat≤1024) (globals : HeapGlobals origin source) :
    RoundLayout (invocationData array heap count stp pad pointers lengths lower upper) ∧
      RoundState (invocationData array heap count stp pad pointers lengths lower upper) origin (loopEntry source heap count) 0 := by
  let data:=invocationData array heap count stp pad pointers lengths lower upper
  have layout : RoundLayout data := ⟨geometry.hs,geometry.hsAligned,geometry.hashes,geometry.hashesAligned,before,geometry.hsBefore,
    stateBefore,padBefore,aligned,inputLower,small,lengthLimits⟩
  have cells:=loopEntry_cells source heap count array arrayCell countCell
  have nextFrame : HashInput.Frame source (loopEntry source heap count) lower upper := ⟨by intro query low high; rfl⟩
  have nextRows:=rows.of_frame source (loopEntry source heap count) array pointers lengths count.toNat lower upper nextFrame
  have nextEnvironment : CurrentKeccak.Hash.Environment (loopEntry source heap count) stp pad :=
    ⟨arena.code,arena.domain,(loopEntry_globals source heap count _ (by decide)).trans environment.stateGlobal,
      (loopEntry_globals source heap count _ (by decide)).trans environment.padGlobal,
      environment.stateArena,environment.padArena,environment.stateAligned,environment.padAligned⟩
  refine ⟨layout,loopEntry_arena source heap count arena,nextEnvironment,
    frame.trans origin source (loopEntry source heap count) lower upper nextFrame,nextRows,?_,cells.1,?_,cells.2.2.1,cells.2.2.2.1,cells.2.2.2.2,?_⟩
  · exact ⟨entryHeap heap count,loopEntry_heap source heap count,geometry.heapBound,geometry.heapAligned,geometry.hashesBefore⟩
  · simpa [data,invocationData] using cells.2.1
  · intro key other
    exact (loopEntry_globals source heap count key other).trans (globals key other)

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.initial_round
