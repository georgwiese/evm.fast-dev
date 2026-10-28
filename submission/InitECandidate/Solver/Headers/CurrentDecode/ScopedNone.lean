import InitECandidate.Solver.Headers.CurrentDecode.Call

namespace InitECandidate.Solver.Headers.CurrentDecode
open Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

theorem scoped_none (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap : BitVec 64) (arena : CurrentStartup.ArenaState source)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (before : pointer.toNat+length.toNat≤heap.toNat)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (Rlp.Header.values pointer length))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "decode_header") expressions continuation)=(none,post)) :
    ∃ target record inner,Returned source target heap record length.toNat ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word record))) continuation=(none,inner) ∧
      post=restore source name inner := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "decode_header") body .one pointer length (original_code source.code arena.code)
  let entry:=callEntryStateHOLFinite source callee
  have ready : CurrentStartup.ArenaState entry := arena.of_frame rfl
  obtain ⟨funded,target,value,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_none source post name .one (ofString "decode_header") expressions _ body continuation callee .one args called run
  obtain ⟨record,answer,afterHeap,room,aligned,nextArena,nextHeap,memory,globals,domain,endian,growth⟩:=
    normal_frame entry target pointer length heap pointerLocal lengthLocal ready heapGlobal heapBound heapLower heapAligned before value bodyRun
  have price:=body_cost entry pointer length heap pointerLocal lengthLocal ready heapGlobal heapBound heapLower heapAligned before
  have forward:=evaluateHOLFiniteState_clock_le entry body
  rw [bodyRun] at price forward
  change source.clock-1-target.clock≤195*length.toNat+473 at price
  change target.clock≤source.clock-1 at forward
  rw [answer] at continued
  exact ⟨target,record,inner,⟨afterHeap,room,aligned,nextArena,nextHeap,memory,globals,domain,endian,growth,(by omega),(by omega)⟩,continued,endpoint⟩

end InitECandidate.Solver.Headers.CurrentDecode

#print axioms InitECandidate.Solver.Headers.CurrentDecode.scoped_none
