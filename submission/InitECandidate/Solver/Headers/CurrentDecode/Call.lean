import InitECandidate.Solver.Headers.CurrentDecode.Normal
import InitECandidate.Solver.Headers.CurrentDecode.Cost
import InitECandidate.Solver.Input.ScopedCallTrace

namespace InitECandidate.Solver.Headers.CurrentDecode
open Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

structure Returned (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap record : BitVec 64) (bytes : Nat) : Prop where
  afterHeap : heap.toNat≤record.toNat
  room : record.toNat+248≤2952790016
  aligned : record.toNat%8=0
  arena : CurrentStartup.ArenaState target
  heapGlobal : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded record 248#64)))
  memory : ∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query
  globals : ∀ key,key≠ofString "heap_ptr" → target.globals.lookup key=source.globals.lookup key
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  growth : (PersistentAlloc.rounded record 248#64).toNat≤heap.toNat+616
  forward : target.clock≤source.clock
  cost : source.clock-target.clock≤251*bytes+474

/-- Every scoped outcome is charged, while any reached continuation receives
its actual fresh header and the frame established by that same decode. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap : BitVec 64) (arena : CurrentStartup.ArenaState source)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (before : pointer.toNat+length.toNat≤heap.toNat)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (Rlp.Header.values pointer length))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "decode_header") expressions continuation)=(result,post)) :
    source.clock-post.clock≤251*length.toNat+474 ∨ ∃ target record inner,
      Returned source target heap record length.toNat ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word record))) continuation=(result,inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "decode_header") body .one pointer length (original_code source.code arena.code)
  let entry:=callEntryStateHOLFinite source callee
  have ready : CurrentStartup.ArenaState entry := arena.of_frame rfl
  have price:=body_cost entry pointer length heap pointerLocal lengthLocal ready heapGlobal heapBound heapLower heapAligned before
  rcases CallNormal.scoped_trace source post name .one (ofString "decode_header") expressions _ body continuation callee .one (251*length.toNat+473) args called price result run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,value,inner,funded,bodyRun,checked,forward,cost,continued,endpoint⟩:=reached
    obtain ⟨record,answer,afterHeap,room,aligned,nextArena,nextHeap,memory,globals,domain,endian,growth⟩:=
      normal_frame entry target pointer length heap pointerLocal lengthLocal ready heapGlobal heapBound heapLower heapAligned before value bodyRun
    rw [answer] at continued
    exact Or.inr ⟨target,record,inner,⟨afterHeap,room,aligned,nextArena,nextHeap,memory,globals,domain,endian,growth,forward,cost⟩,continued,endpoint⟩

/-- A genuine enclosing return must reach the real child return and its
original continuation; a small stopped-cost alternative is insufficient. -/
theorem scoped_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap : BitVec 64) (arena : CurrentStartup.ArenaState source)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (before : pointer.toNat+length.toNat≤heap.toNat)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (Rlp.Header.values pointer length))
    (returned : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "decode_header") expressions continuation)=(some (.returned returned),post)) :
    ∃ target record inner,Returned source target heap record length.toNat ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word record))) continuation=(some (.returned returned),inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "decode_header") body .one pointer length (original_code source.code arena.code)
  let entry:=callEntryStateHOLFinite source callee
  have ready : CurrentStartup.ArenaState entry := arena.of_frame rfl
  obtain ⟨funded,target,value,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_normal source post name .one (ofString "decode_header") expressions _ body continuation callee .one args called returned run
  obtain ⟨record,answer,afterHeap,room,aligned,nextArena,nextHeap,memory,globals,domain,endian,growth⟩:=
    normal_frame entry target pointer length heap pointerLocal lengthLocal ready heapGlobal heapBound heapLower heapAligned before value bodyRun
  have price:=body_cost entry pointer length heap pointerLocal lengthLocal ready heapGlobal heapBound heapLower heapAligned before
  have forward:=evaluateHOLFiniteState_clock_le entry body
  rw [bodyRun] at price forward
  change source.clock-1-target.clock≤251*length.toNat+473 at price
  change target.clock≤source.clock-1 at forward
  rw [answer] at continued
  exact ⟨target,record,inner,⟨afterHeap,room,aligned,nextArena,nextHeap,memory,globals,domain,endian,growth,(by omega),(by omega)⟩,continued,endpoint⟩

end InitECandidate.Solver.Headers.CurrentDecode

#print axioms InitECandidate.Solver.Headers.CurrentDecode.scoped_trace
#print axioms InitECandidate.Solver.Headers.CurrentDecode.scoped_returned
