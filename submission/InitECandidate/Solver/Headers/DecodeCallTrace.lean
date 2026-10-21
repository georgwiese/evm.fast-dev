import InitECandidate.Solver.Headers.DecodeReturned
import InitECandidate.Solver.Headers.DecodeCallCost

namespace InitECandidate.Solver.Headers.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Data derived from a genuine original header return, relative to the
same current caller and incoming heap frontier. -/
structure Returned (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit : BitVec 64) (cutoff : Nat) (output : BitVec 64) : Prop where
  allocation : AllocatedBytes.Arena output 248
  aligned : output.toNat%8=0
  afterHeap : heap.toNat≤output.toNat
  heapGlobal : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded output 248#64)))
  arena : Rlp.Validation.Arena target cursor limit
  memory : Input.HashInput.Frame source target cutoff heap.toNat
  globals : ∀ key,key≠ofString "heap_ptr" → target.globals.lookup key=source.globals.lookup key
  code : target.code=source.code
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  exceptions : target.eshapes=source.eshapes
  forward : target.clock≤source.clock
  cost : source.clock-target.clock≤251*length.toNat+1374

/-- Every original scoped decoder outcome either stops within its own
bound or reaches its real continuation with the actual allocated header
and full preserved preceding-memory/global context. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit : BitVec 64) (cutoff : Nat)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (Rlp.Header.values pointer length))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (inputLower : 2701131776≤pointer.toNat) (heapAligned : heap.toNat%8=0)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (shape : source.eshapes.lookup (ofString "HdrErr")=some .one)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "decode_header") expressions continuation)=(result,post)) :
    source.clock-post.clock≤251*length.toNat+1374 ∨
      ∃ target output inner,Returned source target pointer length heap cursor limit cutoff output ∧
        evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name (.val (.word output))) continuation=(result,inner) ∧
        post=WitnessRadix.QueryBranch.restore source name inner := by
  obtain ⟨callee,called,pointerCell,lengthCell⟩ := Rlp.environment source.code.lookup (ofString "decode_header") body .one pointer length (original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have ready:=Rlp.Validation.Arena.of_fields source entry cursor limit arena rfl rfl
  have price:=body_cost entry pointer length heap cursor limit cutoff pointerCell lengthCell ready heapGlobal heapBound before sizeBound inputLower heapAligned aligned scratchBelow inputAbove installed shape
  rcases Input.CallNormal.scoped_trace source post name .one (ofString "decode_header") expressions _ body continuation callee .one (251*length.toNat+1373) args called price result run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩ := reached
    obtain ⟨output,valueEq,allocation,outputAligned,afterHeap,nextHeap,nextArena,memory,globals⟩ :=
      body_returned entry target pointer length heap cursor limit cutoff pointerCell lengthCell ready heapGlobal heapBound before sizeBound inputLower heapAligned aligned scratchBelow inputAbove installed value bodyRun
    rw [valueEq] at continued
    have fields:=Input.evaluation_fields entry target body (some (.returned value)) bodyRun
    exact Or.inr ⟨target,output,inner,⟨allocation,outputAligned,afterHeap,nextHeap,nextArena,⟨memory.words⟩,globals,fields.2.2.2,fields.1,fields.2.1,fields.2.2.1,forward,cost⟩,continued,endpoint⟩

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.scoped_trace
