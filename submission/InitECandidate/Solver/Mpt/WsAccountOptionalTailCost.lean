import InitECandidate.Solver.Mpt.WsAccountOptionalProgram
import InitECandidate.Solver.Mpt.TrieWalkValues
import InitECandidate.Solver.WitnessRadix.AllocationNormal
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 10000

/-- The actual original account allocation derives room, its output geometry,
new heap and real continuation before invoking the unchanged decoder. -/
theorem after_guard_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length heap cursor limit : BitVec 64) (cutoff : Nat)
    (leafCell : source.locals.lookup (ofString "leaf")=some (TrieWalk.triple 1#64 pointer length))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterGuard).2.clock≤191*length.toNat+295 := by
  obtain ⟨callee,called,n⟩ := PersistentAlloc.environment source.code.lookup 56#64 (PersistentAlloc.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.const 56#64]=some (PersistentAlloc.values 56#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  rw [after_guard_shape]
  have joined := Input.ClockCost.scoped_reached_current source "a" .one (ofString "alloc") [.const 56#64] _ PersistentAlloc.body afterAlloc callee .one
    1 (191*length.toNat+293) args called (PersistentAlloc.body_price source.code installed _ rfl) (by
      intro target returned normal checked
      obtain ⟨returnedEq,room,frame⟩ := PersistentAlloc.post_of_normal (callEntryStateHOLFinite source callee) target heap 56#64 n heapGlobal heapBound
        (Input.Trap.original_code source.code installed) returned normal
      subst returned
      let ready := Input.CallNormal.continuationEntry source target "a" (.val (.word heap))
      have globalsEq := congrArg PanSemStateFiniteExact.globals frame
      change target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 56#64))) at globalsEq
      have domainEq := congrArg PanSemStateFiniteExact.memaddrs frame
      change target.memaddrs=source.memaddrs at domainEq
      have nextArena := Rlp.Validation.Arena.heap_updated source ready cursor limit (PersistentAlloc.rounded heap 56#64) arena domainEq globalsEq
      have nextHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 56#64))) := by
        change target.globals.lookup (ofString "heap_ptr")=_
        rw [globalsEq]
        simp [HolFiniteMapExact.update,FUPDATE]
      have guards := PersistentAlloc.guards heap 56#64 room
      have nextLeaf : ready.locals.lookup (ofString "leaf")=some (TrieWalk.triple 1#64 pointer length) :=
        (Input.CallNormal.continuation_lookup_other source target "a" "leaf" (.val (.word heap)) (by decide)).trans leafCell
      have outputCell : ready.locals.lookup (ofString "a")=some (.val (.word heap)) := Input.CallNormal.continuation_lookup_same _ _ _ _
      have decodeArgs : evalListHOLFinite ready (h:=fun address=>Classical.propDecidable (ready.memaddrs address)) decodeArguments=some (AccountDecode.values pointer length heap) := by
        simp [decodeArguments,field,AccountDecode.values,TrieWalk.triple,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,nextLeaf,outputCell]
      have output : AccountDecode.Output heap := ⟨heapLower,room,heapAligned⟩
      have codeEq := (Input.evaluation_fields _ target PersistentAlloc.body _ normal).2.2.2
      have nextInstalled : Input.OriginalCode.Installed ready.code := by change Input.OriginalCode.Installed target.code; rw [codeEq]; exact installed
      have price := AccountDecode.call_cost ready pointer length (PersistentAlloc.rounded heap 56#64) cursor limit heap cutoff nextArena nextHeap
        guards.2.2.2.1 (by have := guards.2.2.1; change heap.toNat+56≤_ at this; omega) sizeBound aligned scratchBelow inputAbove output nextInstalled
        (some none) decodeArguments decodeArgs
      rw [after_alloc_shape]
      have total := Input.ClockCost.sequence_current ready decode (.return (localVar "a")) (191*length.toNat+293) 0 price (Input.ClockCost.returned ready.code _)
      simpa only [ready,Input.CallNormal.continuationEntry,setVarHOLFinite_clock,Nat.add_zero] using total)
  omega

theorem after_leaf_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit : BitVec 64) (cutoff valueLimit : Nat)
    (answer : ValueHOL 64) (leafCell : source.locals.lookup (ofString "leaf")=some answer)
    (result : TrieWalk.Answer source.memaddrs valueLimit answer (fun p n=>cutoff≤p.toNat ∧ p.toNat+n.toNat≤heap.toNat))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (sizeBound : 16*valueLimit<2^64) (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterLeaf).2.clock≤191*valueLimit+295 := by
  rcases result with absent | ⟨pointer,length,found,payload,inputAbove,before⟩
  · rw [absent] at leafCell
    rw [after_leaf_shape,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
    simp [field,evalHOLExact,evalListHOLExact,localVar,toExact,leafCell,TrieWalk.triple,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_return,shapeOfHOLExact,sizeOfShapeWithContextHOL,emptyLocalsHOLFinite]
  · rw [found] at leafCell
    have price := after_guard_cost source pointer length heap cursor limit cutoff leafCell arena heapGlobal heapBound heapLower heapAligned before
      (by have := payload.1; omega) aligned scratchBelow inputAbove installed
    have cost := Input.ClockCost.stopping_guard_current source (.cmp .equal (field 0) (.const 0#64)) (.return (.const 1#64)) afterGuard 0
      (191*length.toNat+295) (Input.NoFallthrough.returned (.const 1#64) source) ((Input.ClockCost.returned source.code _) source rfl) price
    rw [after_leaf_shape]
    have := payload.1
    change source.clock-(evaluateHOLFiniteState source (.seq _ _)).2.clock≤_ at cost
    omega

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.after_guard_cost
#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.after_leaf_cost
