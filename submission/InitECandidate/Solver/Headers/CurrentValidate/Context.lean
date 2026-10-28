import InitECandidate.Solver.Headers.CurrentValidate.Returned
import InitECandidate.Solver.Headers.CurrentValidate.CallCost

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix

/-- The current physical validator entry. All fields concern the reached
state or fixed input geometry; none describes a future successful phase. -/
structure Context (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper : Nat) : Prop where
  arena : CurrentStartup.ArenaState source
  environment : CurrentKeccak.Hash.Environment source stp pad
  rows : Rows source array pointers lengths count.toNat lower upper
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapLower : 2701131776≤heap.toNat
  heapBound : heap.toNat≤2952790016
  heapAligned : heap.toNat%8=0
  before : upper≤heap.toNat
  stateBefore : stp.toNat+200≤lower
  padBefore : pad.toNat+136≤lower
  aligned : lower%8=0
  inputLower : 2701131776≤lower
  lengthLimits : ∀ index<count.toNat,(lengths index).toNat≤1024

theorem Context.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {array heap count stp pad : BitVec 64} {pointers lengths : Nat→BitVec 64} {lower upper : Nat}
    (ready : Context source array heap count stp pad pointers lengths lower upper)
    (same : LocalEffects.erase target=LocalEffects.erase source) : Context target array heap count stp pad pointers lengths lower upper := by
  have globals:=congrArg PanSemStateFiniteExact.globals same
  change target.globals=source.globals at globals
  have nextRows:=ready.rows.of_frame source target array pointers lengths count.toNat lower upper
    ⟨fun query _ _=>congrFun (LocalEffects.memory_of_erase source target same) query⟩
  exact ⟨ready.arena.of_frame same,ready.environment.of_frame same,nextRows,by rw [globals]; exact ready.heapCell,
    ready.heapLower,ready.heapBound,ready.heapAligned,ready.before,ready.stateBefore,ready.padBefore,ready.aligned,ready.inputLower,ready.lengthLimits⟩

/-- Normal completion supplies the actual tuple and advanced physical
context, with all original records/earlier input and nonheap globals intact. -/
theorem Context.returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper : Nat)
    (ready : Context source array heap count stp pad pointers lengths lower upper)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=result heap (hashesPointer heap count) ∧ count.toNat≤256 ∧ Geometry heap count ∧
      ∃ nextHeap,Context post array nextHeap count stp pad pointers lengths lower upper ∧ heap.toNat≤nextHeap.toNat ∧
        HashInput.Frame source post lower upper ∧ HeapGlobals source post := by
  obtain ⟨answer,small,geometry,finish,index,bounded,state,erased⟩:=body_returned source post array heap count stp pad pointers lengths lower upper
    ready.arena ready.environment ready.rows arrayCell countCell ready.heapCell ready.heapLower ready.heapBound ready.heapAligned ready.before
    ready.stateBefore ready.padBefore ready.aligned ready.inputLower ready.lengthLimits value normal
  have globals:=congrArg PanSemStateFiniteExact.globals erased
  change post.globals=finish.globals at globals
  have memory:=LocalEffects.memory_of_erase finish post erased
  obtain ⟨nextHeap,nextCell,nextBound,nextAligned,nextBefore⟩:=state.heap
  have first:=geometry.hsBefore
  have monotone : heap.toNat≤nextHeap.toNat := by
    change (hashesPointer heap count).toNat+32*count.toNat+32≤nextHeap.toNat at nextBefore
    omega
  have frame : HashInput.Frame source post lower upper := ⟨fun query low high=>(congrFun memory query).trans (state.input.words query low high)⟩
  have postRows : Rows post array pointers lengths count.toNat lower upper :=
    ready.rows.of_frame source post array pointers lengths count.toNat lower upper frame
  have postContext : Context post array nextHeap count stp pad pointers lengths lower upper :=
    ⟨state.arena.of_frame erased,state.environment.of_frame erased,postRows,by rw [globals]; exact nextCell,
      (by have low:=ready.heapLower; omega),nextBound,nextAligned,(by have before:=ready.before; omega),
      ready.stateBefore,ready.padBefore,ready.aligned,ready.inputLower,ready.lengthLimits⟩
  exact ⟨answer,small,geometry,nextHeap,postContext,monotone,frame,by intro key different; rw [globals]; exact state.globals key different⟩

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.Context.of_frame
#print axioms InitECandidate.Solver.Headers.CurrentValidate.Context.returned
