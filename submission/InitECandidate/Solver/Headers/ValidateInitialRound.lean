import InitECandidate.Solver.Headers.ValidateRound

namespace InitECandidate.Solver.Headers.Validate
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

def invocationData (array heap count cursor limit stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper : Nat) : Data := {
  array:=array,hs:=heap,hashes:=hashesPointer heap count,cursor:=cursor,limit:=limit,stp:=stp,pad:=pad,
  pointers:=pointers,lengths:=lengths,count:=count.toNat,lower:=lower,upper:=upper }

/-- The real allocation-prefix state supplies the first loop invariant.
Only current caller rows, initialized hash workspace and the derived actual
allocator geometry are required. No loop/header/hash success is assumed. -/
theorem initial_round (origin source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count cursor limit stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper : Nat)
    (installed : Input.OriginalCode.Installed source.code)
    (shape : source.eshapes.lookup (ofString "HdrErr")=some .one)
    (arena : Rlp.Validation.Arena source cursor limit) (environment : Keccak256.Environment source stp pad)
    (frame : Input.HashInput.Frame origin source lower upper) (rows : Rows source array pointers lengths count.toNat lower upper)
    (geometry : Geometry heap count)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (before : upper≤heap.toNat) (small : count.toNat≤256)
    (stateArena : AllocatedBytes.Arena stp 200) (stateAligned : stp.toNat%8=0)
    (padArena : AllocatedBytes.Arena pad 136) (padAligned : pad.toNat%8=0)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (aligned : lower%8=0) (inputLower : 2701131776≤lower) (scratchBefore : cursor.toNat≤lower) :
    RoundLayout (invocationData array heap count cursor limit stp pad pointers lengths lower upper) ∧
      RoundState (invocationData array heap count cursor limit stp pad pointers lengths lower upper) origin (loopEntry source heap count) 0 := by
  let data:=invocationData array heap count cursor limit stp pad pointers lengths lower upper
  have layout : RoundLayout data := ⟨geometry.hs,geometry.hsAligned,geometry.hashes,geometry.hashesAligned,before,geometry.hsBefore,
    stateArena,stateAligned,padArena,padAligned,stateBefore,padBefore,aligned,inputLower,small,scratchBefore⟩
  have cells:=loopEntry_cells source heap count array arrayCell countCell
  have nextFrame : Input.HashInput.Frame source (loopEntry source heap count) lower upper := ⟨by intro query low high; rfl⟩
  have nextRows:=rows.of_frame source (loopEntry source heap count) array pointers lengths count.toNat lower upper nextFrame
  have nextEnvironment:=Keccak256.Environment.of_fields source (loopEntry source heap count) stp pad environment rfl rfl rfl
    (loopEntry_globals source heap count)
  refine ⟨layout,installed,shape,loopEntry_arena source heap count cursor limit arena,nextEnvironment,
    frame.trans origin source (loopEntry source heap count) lower upper nextFrame,nextRows,?_,cells.1,?_,cells.2.2.1,cells.2.2.2.1,cells.2.2.2.2⟩
  · exact ⟨entryHeap heap count,loopEntry_heap source heap count,geometry.heapBound,geometry.heapAligned,geometry.hashesBefore⟩
  · simpa [data,invocationData] using cells.2.1

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.initial_round
