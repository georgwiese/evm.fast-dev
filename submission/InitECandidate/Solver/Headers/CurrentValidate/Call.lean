import InitECandidate.Solver.Headers.CurrentValidate.Context
import InitECandidate.Solver.Input.ScopedCallTrace

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

structure Returned (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count stp pad nextHeap : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper : Nat) : Prop where
  context : Context target array nextHeap count stp pad pointers lengths lower upper
  heapAfter : heap.toNat≤nextHeap.toNat
  countBound : count.toNat≤256
  allocations : Geometry heap count
  input : HashInput.Frame source target lower upper
  globals : HeapGlobals source target
  forward : target.clock≤source.clock
  cost : source.clock-target.clock≤51528323

/-- Every actual scoped validator outcome either stops within its bound
or exposes the genuine arrays, physical continuation state and paid clock.
All later main outcomes are retained in the original continuation. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper : Nat)
    (context : Context source array heap count stp pad pointers lengths lower upper)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some [.val (.word array),.val (.word count)])
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "validate_headers") expressions continuation)=(outcome,post)) :
    source.clock-post.clock≤51528323 ∨ ∃ target nextHeap inner,
      Returned source target array heap count stp pad nextHeap pointers lengths lower upper ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name (result heap (hashesPointer heap count))) continuation=(outcome,inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,arrayCell,countCell⟩:=word_pair_environment source.code.lookup (ofString "validate_headers") (ofString "arr") (ofString "n") body resultShape array count (by decide) (original_code source.code context.arena.code)
  let entry:=callEntryStateHOLFinite source callee
  have ready : Context entry array heap count stp pad pointers lengths lower upper := context.of_frame rfl
  have price:=body_cost entry array heap count stp pad pointers lengths lower upper ready.arena ready.environment ready.rows arrayCell countCell
    ready.heapCell ready.heapLower ready.heapBound ready.heapAligned ready.before ready.stateBefore ready.padBefore ready.aligned ready.inputLower ready.lengthLimits
  rcases CallNormal.scoped_trace source post name resultShape (ofString "validate_headers") expressions _ body continuation callee resultShape 51528322 args called price outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩:=reached
    obtain ⟨answer,small,allocations,nextHeap,next,afterHeap,frame,globals⟩:=ready.returned entry target array heap count stp pad pointers lengths lower upper arrayCell countCell value bodyRun
    rw [answer] at continued
    exact Or.inr ⟨target,nextHeap,inner,⟨next,afterHeap,small,allocations,⟨frame.words⟩,globals,forward,cost⟩,continued,endpoint⟩

/-- Actual enclosing returns must pass through the same genuine validator
return, rather than merely satisfying the stopped-cost alternative. -/
theorem scoped_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper : Nat)
    (context : Context source array heap count stp pad pointers lengths lower upper)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some [.val (.word array),.val (.word count)])
    (finalValue : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "validate_headers") expressions continuation)=(some (.returned finalValue),post)) :
    ∃ target nextHeap inner,Returned source target array heap count stp pad nextHeap pointers lengths lower upper ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name (result heap (hashesPointer heap count))) continuation=(some (.returned finalValue),inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,arrayCell,countCell⟩:=word_pair_environment source.code.lookup (ofString "validate_headers") (ofString "arr") (ofString "n") body resultShape array count (by decide) (original_code source.code context.arena.code)
  let entry:=callEntryStateHOLFinite source callee
  have ready : Context entry array heap count stp pad pointers lengths lower upper := context.of_frame rfl
  obtain ⟨funded,target,value,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_normal source post name resultShape (ofString "validate_headers") expressions _ body continuation callee resultShape args called finalValue run
  obtain ⟨answer,small,allocations,nextHeap,next,afterHeap,frame,globals⟩:=ready.returned entry target array heap count stp pad pointers lengths lower upper arrayCell countCell value bodyRun
  have price:=body_cost entry array heap count stp pad pointers lengths lower upper ready.arena ready.environment ready.rows arrayCell countCell
    ready.heapCell ready.heapLower ready.heapBound ready.heapAligned ready.before ready.stateBefore ready.padBefore ready.aligned ready.inputLower ready.lengthLimits
  have forward:=evaluateHOLFiniteState_clock_le entry body
  rw [bodyRun] at price forward
  change source.clock-1-target.clock≤51528322 at price
  change target.clock≤source.clock-1 at forward
  rw [answer] at continued
  exact ⟨target,nextHeap,inner,⟨next,afterHeap,small,allocations,⟨frame.words⟩,globals,(by omega),(by omega)⟩,continued,endpoint⟩

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.scoped_trace
#print axioms InitECandidate.Solver.Headers.CurrentValidate.scoped_returned
