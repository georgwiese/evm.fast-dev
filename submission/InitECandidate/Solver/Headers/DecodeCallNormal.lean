import InitECandidate.Solver.Headers.DecodeCallTrace
import InitECandidate.Solver.Input.ScopedCallNone

namespace InitECandidate.Solver.Headers.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Actual normal scoped header call derives the real header and its genuine continuation. -/
theorem scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit : BitVec 64) (cutoff : Nat)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (Rlp.Header.values pointer length))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (inputLower : 2701131776≤pointer.toNat) (heapAligned : heap.toNat%8=0)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (shape : source.eshapes.lookup (ofString "HdrErr")=some .one)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "decode_header") expressions continuation)=(none,post)) :
    ∃ target output inner,Returned source target pointer length heap cursor limit cutoff output ∧
        evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name (.val (.word output))) continuation=(none,inner) ∧
        post=WitnessRadix.QueryBranch.restore source name inner := by
  obtain ⟨callee,called,pointerCell,lengthCell⟩ := Rlp.environment source.code.lookup (ofString "decode_header") body .one pointer length (original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have ready:=Rlp.Validation.Arena.of_fields source entry cursor limit arena rfl rfl
  have price:=body_cost entry pointer length heap cursor limit cutoff pointerCell lengthCell ready heapGlobal heapBound before sizeBound inputLower heapAligned aligned scratchBelow inputAbove installed shape
  obtain ⟨funded,target,value,inner,bodyRun,checked,continued,endpoint⟩ := Input.CallNormal.scoped_none source post name .one (ofString "decode_header") expressions _ body continuation callee .one args called run
  have clock:=evaluateHOLFiniteState_clock_le entry body
  rw [bodyRun] at price clock
  change source.clock-1-target.clock≤251*length.toNat+1373 at price
  change target.clock≤source.clock-1 at clock
  have forward : target.clock≤source.clock := by omega
  have cost : source.clock-target.clock≤251*length.toNat+1374 := by omega
  obtain ⟨output,valueEq,allocation,outputAligned,afterHeap,nextHeap,nextArena,memory,globals⟩ :=
    body_returned entry target pointer length heap cursor limit cutoff pointerCell lengthCell ready heapGlobal heapBound before sizeBound inputLower heapAligned aligned scratchBelow inputAbove installed value bodyRun
  rw [valueEq] at continued
  have fields:=Input.evaluation_fields entry target body (some (.returned value)) bodyRun
  exact ⟨target,output,inner,⟨allocation,outputAligned,afterHeap,nextHeap,nextArena,⟨memory.words⟩,globals,fields.2.2.2,fields.1,fields.2.1,fields.2.2.1,Input.evaluation_oracle entry target body (some (.returned value)) bodyRun,forward,cost⟩,continued,endpoint⟩

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.scoped_normal
