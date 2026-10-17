import InitECandidate.Solver.Input.RequestOffsetsStores

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessRadix.ProgramPrefix

theorem command_single (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (code : ProgHOL 64)
    (run : evaluateHOLFiniteState source code=(none,post)) (clock : post.clock≤source.clock) :
    Executes source [.command code] post id := Executes.command run clock (Executes.done _)

theorem command_prepend (source post entered : PanSemStateFiniteExact 64 Guest.HostMemory) (code : ProgHOL 64)
    (rest : List Action) (run : evaluateHOLFiniteState source code=(none,post)) (clock : post.clock≤source.clock)
    (next : Executes post rest entered id) : Executes source (.command code::rest) entered id := Executes.command run clock next

set_option maxHeartbeats 20000

/-- Actual request declarations and all three word stores, including their
lexical scopes, copied-input frame and concrete validator array. -/
theorem offsets_setup (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer array : BitVec 64)
    (heap : Blob.HeapInput source input pointer) (inside : 62≤input.length%2^64)
    (np : source.locals.lookup (ofString "np")=some (.val (.word (pointer+18#64))))
    (arrayGlobal : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (upper : pointer.toNat+input.length%2^64+8≤33806089496)
    (arrayLower : 2701131776≤array.toNat) (arrayBefore : array.toNat+64≤pointer.toNat) :
    Executes source offsetActions (offsetsStored source input array) (restoreOffsets source input) ∧
    Blob.HeapInput (offsetsStored source input array) input pointer ∧
    (∀ position<3,source.memaddrs (array+BitVec.ofNat 64 (8*position))) ∧
    (∀ position<3,(offsetsStored source input array).memory (array+BitVec.ofNat 64 (8*position))=.word (requestWords input position)) := by
  have r0:=request_read source input pointer [] 18 heap (by omega) np rfl
  have firstHeap : Blob.HeapInput (offsetFirst source input) input pointer := heap
  have firstNp : (offsetFirst source input).locals.lookup (ofString "np")=some (.val (.word (pointer+18#64))) :=
    (bind_lookup_other source "o_pl" "np" _ (by decide)).trans np
  have r1:=request_read (offsetFirst source input) input pointer [4] 22 firstHeap (by omega) firstNp rfl
  have secondHeap : Blob.HeapInput (offsetSecond source input) input pointer := heap
  have secondNp : (offsetSecond source input).locals.lookup (ofString "np")=some (.val (.word (pointer+18#64))) :=
    (bind_lookup_other (offsetFirst source input) "o_vh" "np" _ (by decide)).trans firstNp
  have r2:=request_read (offsetSecond source input) input pointer [40] 58 secondHeap (by omega) secondNp rfl
  obtain ⟨s0,s1,s2,storedHeap,mapped,cells⟩:=offsets_stores source input pointer array heap arrayGlobal domain pointerAligned arrayAligned upper arrayLower arrayBefore
  have last : Executes (hashesStored source input array) [.command storeRequests] (offsetsStored source input array) id :=
    command_single (hashesStored source input array) (offsetsStored source input array) storeRequests s2 (Nat.le_refl source.clock)
  have middle : Executes (payloadStored source input array) [.command storeHashes,.command storeRequests] (offsetsStored source input array) id :=
    command_prepend (payloadStored source input array) (hashesStored source input array) (offsetsStored source input array) storeHashes [.command storeRequests] s1 (Nat.le_refl source.clock) last
  have stores : Executes (offsetLoaded source input) [.command storePayload,.command storeHashes,.command storeRequests] (offsetsStored source input array) id :=
    command_prepend (offsetLoaded source input) (payloadStored source input array) (offsetsStored source input array) storePayload [.command storeHashes,.command storeRequests] s0 (Nat.le_refl source.clock) middle
  refine ⟨?_,storedHeap,mapped,cells⟩
  unfold offsetActions restoreOffsets
  refine Executes.declare (restoreRest:=fun target=>restore (offsetFirst source input) "o_vh" (restore (offsetSecond source input) "o_rq" target)) (requestWords input 0) r0 ?_
  refine Executes.declare (restoreRest:=fun target=>restore (offsetSecond source input) "o_rq" target) (requestWords input 1) r1 ?_
  refine Executes.declare (restoreRest:=id) (requestWords input 2) r2 ?_
  exact stores

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.offsets_setup

#print axioms InitECandidate.Solver.Input.Request.command_single
#print axioms InitECandidate.Solver.Input.Request.command_prepend
