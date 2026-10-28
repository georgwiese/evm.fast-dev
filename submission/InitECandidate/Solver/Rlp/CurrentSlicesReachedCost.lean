import InitECandidate.Solver.Rlp.CurrentSlicesMemory
import InitECandidate.Solver.Input.ClockCostScopedReached

namespace InitECandidate.Solver.Rlp.CurrentSlices
open Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

/-- Only real normal conversion returns supply the records, allocator room
and physical caller state used to price their true suffix. All other outcomes
remain in the converter allowance. -/
theorem scoped_frame_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap : BitVec 64) (arena : CurrentStartup.ArenaState source)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (before : pointer.toNat+length.toNat≤heap.toNat)
    (sizeBound : 16*length.toNat<2^64)
    (name : String) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (Header.values pointer length))
    (tail : ∀ target : PanSemStateFiniteExact 64 Guest.HostMemory,∀ items : List ListItem,∀ count : BitVec 64,
      ListItems target pointer length.toNat items → count.toNat=items.length → count.toNat≤length.toNat →
      Records target.memory heap pointer items → heap.toNat+16*count.toNat≤2952790016 → CurrentStartup.ArenaState target →
      target.memaddrs=source.memaddrs → target.be=source.be →
      target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (count*16#64)))) →
      let ready:=CallNormal.continuationEntry source target name (Slices.result heap count)
      ready.clock-(evaluateHOLFiniteState ready continuation).2.clock≤tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) resultShape (ofString "rlp_list_to_slices") expressions continuation)).2.clock≤57*length.toNat+tailPrice+4 := by
  have fits : pointer.toNat+length.toNat<2^64 := by have h:=heap.isLt; omega
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "rlp_list_to_slices") body resultShape pointer length (original_code source.code arena.code)
  have price:=body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits arena.code
  have actual:=ClockCost.scoped_reached_current source name resultShape (ofString "rlp_list_to_slices") expressions (Header.values pointer length) body continuation callee resultShape (57*length.toNat+3) tailPrice args called price ?_
  · omega
  · intro target value normal checked
    obtain ⟨items,count,model,countEq,countBound,valueEq,records,room,nextArena,globals,frame,metadata,cost⟩:=body_normal (callEntryStateHOLFinite source callee) target pointer length heap pointerLocal lengthLocal (arena.of_frame rfl) heapGlobal heapBound before sizeBound value normal
    have fields:=evaluation_fields (callEntryStateHOLFinite source callee) target body (some (.returned value)) normal
    rw [valueEq]
    exact tail target items count model countEq countBound records room nextArena fields.1 fields.2.1 globals

end InitECandidate.Solver.Rlp.CurrentSlices

#print axioms InitECandidate.Solver.Rlp.CurrentSlices.scoped_frame_cost
