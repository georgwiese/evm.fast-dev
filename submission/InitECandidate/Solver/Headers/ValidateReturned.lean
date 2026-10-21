import InitECandidate.Solver.Headers.ValidateEntryReturned
import InitECandidate.Solver.Headers.ValidateLoopReturned
import InitECandidate.Solver.Headers.ValidateInitialRound

namespace InitECandidate.Solver.Headers.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Physical output of the unchanged validator. The array pointers are the
actual incoming heap and its first rounded allocation, even for zero rows. -/
structure Output (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count cursor limit stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper : Nat) : Prop where
  smallCount : count.toNat≤256
  geometry : Geometry heap count
  currentHeap : ∃ current,target.globals.lookup (ofString "heap_ptr")=some (.val (.word current)) ∧
    current.toNat≤33806089496 ∧ current.toNat%8=0 ∧ (hashesPointer heap count).toNat+32*count.toNat+32≤current.toNat
  arena : Rlp.Validation.Arena target cursor limit
  environment : Keccak256.Environment target stp pad
  memory : Input.HashInput.Frame source target lower upper
  rows : Rows target array pointers lengths count.toNat lower upper
  globals : HeapGlobals source target

/-- The complete original body returns its real pointer pair and preserves
the input, scratch and initialized hash environment. Actual successful
allocations are derived from the observed return, rather than assumed. -/
theorem body_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count cursor limit stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper : Nat)
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
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=result heap (hashesPointer heap count) ∧ Output source post array heap count cursor limit stp pad pointers lengths lower upper := by
  obtain ⟨small,funded,firstRoom,secondRoom,inner,continued,endpoint⟩ := entry_returned source post heap count countCell heapCell heapBound installed value normal
  have geometry:=geometry_of_room heap count small heapLower heapAligned firstRoom secondRoom
  obtain ⟨layout,state⟩ := initial_round source source array heap count cursor limit stp pad pointers lengths lower upper installed shape arena environment
    (Input.HashInput.Frame.refl source lower upper) rows geometry arrayCell countCell before small stateArena stateAligned padArena padAligned stateBefore padBefore aligned inputLower scratchBefore (HeapGlobals.refl source)
  let data:=invocationData array heap count cursor limit stp pad pointers lengths lower upper
  obtain ⟨valueEq,finish,index,bounded,finalState,innerEnd⟩ := loops_returned data source (loopEntry source heap count) inner state layout value continued
  have same : Input.LocalEffects.erase post=Input.LocalEffects.erase finish := by rw [endpoint,innerEnd]; rfl
  have domain:=congrArg PanSemStateFiniteExact.memaddrs same
  have globals:=congrArg PanSemStateFiniteExact.globals same
  have code:=congrArg PanSemStateFiniteExact.code same
  have oracle:=congrArg (fun current=>current.ffi.oracle) same
  change post.memaddrs=finish.memaddrs at domain
  change post.globals=finish.globals at globals
  change post.code=finish.code at code
  change post.ffi.oracle=finish.ffi.oracle at oracle
  have memory:=Input.LocalEffects.memory_of_erase finish post same
  have frame : Input.HashInput.Frame finish post lower upper := ⟨by intro query low high; rw [memory]⟩
  refine ⟨valueEq,small,geometry,?_,?_,?_,?_,?_,?_⟩
  · obtain ⟨current,cell,bound,alignment,afterHashes⟩ := finalState.heap
    exact ⟨current,by rw [globals]; exact cell,bound,alignment,afterHashes⟩
  · exact Rlp.Validation.Arena.of_fields finish post cursor limit finalState.arena domain globals
  · exact Keccak256.Environment.of_fields finish post stp pad finalState.environment domain code oracle (by intro key other; rw [globals])
  · exact finalState.input.trans source finish post lower upper frame
  · exact finalState.rows.of_frame finish post array pointers lengths count.toNat lower upper frame
  · intro key other
    rw [globals]
    exact finalState.globals key other

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.body_returned
