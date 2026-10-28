import InitECandidate.Solver.Headers.CurrentDecode.AfterListCost
import InitECandidate.Solver.Rlp.CurrentSlicesReachedCost

namespace InitECandidate.Solver.Headers.CurrentDecode
open Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 10000 in
/-- Complete current slicing/count/allocation/field suffix. The actual
normal converter return supplies its record image and next heap; every failed
converter or allocation stays inside its own checked allowance. -/
theorem after_kind_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer header payload heap : BitVec 64)
    (topCell : source.locals.lookup (ofString "top")=some (Rlp.Item.result pointer header payload 1#64))
    (arena : CurrentStartup.ArenaState source)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (before : (pointer+header).toNat+payload.toNat≤heap.toNat) :
    source.clock-(evaluateHOLFiniteState source afterKind).2.clock≤149*payload.toNat+460 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) listArguments=some (Rlp.Header.values (pointer+header) payload) := by
    simp [listArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,topCell,Rlp.Item.result]
  rw [after_top_shape.2]
  have actual:=Rlp.CurrentSlices.scoped_frame_cost source (pointer+header) payload heap arena heapGlobal heapBound before (by omega)
    "lst" listArguments afterList (92*payload.toNat+456) args ?_
  · have arithmetic : ∀ n : Nat,57*n+(92*n+456)+4≤149*n+460 := by intro n; omega
    exact Nat.le_trans actual (arithmetic payload.toNat)
  · intro target items count model countEq countBound records room nextArena domain endian globals
    let ready:=CallNormal.continuationEntry source target "lst" (Rlp.Slices.result heap count)
    have inputFits : (pointer+header).toNat+payload.toNat<2^64 := by have h:=heap.isLt; omega
    have arrayArena : AllocatedBytes.Arena heap (16*items.length) := ⟨heapLower,by omega⟩
    have image : CurrentHelpers.SliceImage target (pointer+header) heap payload.toNat items :=
      ⟨model,records,nextArena,arrayArena,heapAligned,inputFits,before⟩
    have readyImage : CurrentHelpers.SliceImage ready (pointer+header) heap payload.toNat items := image.of_frame rfl
    have listCell : ready.locals.lookup (ofString "lst")=some (Rlp.Slices.result heap count) := by
      simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    have product : (count*16#64).toNat=16*count.toNat := by
      rw [BitVec.toNat_mul,Nat.mod_eq_of_lt (by change count.toNat*16<2^64; omega)]
      change count.toNat*16=16*count.toNat
      omega
    have allocationRoom : heap.toNat+(count*16#64).toNat≤2952790016 := by rw [product]; exact room
    have guards:=PersistentAlloc.guards heap (count*16#64) allocationRoom
    have readyHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (count*16#64)))) := by
      change target.globals.lookup _=_
      rw [globals]
      simp [HolFiniteMapExact.update,FUPDATE]
    exact after_list_cost ready (pointer+header) heap (PersistentAlloc.rounded heap (count*16#64)) count payload.toNat items readyImage countEq listCell readyHeap
      guards.2.2.2.1 (by rw [←countEq]; rw [←product]; exact guards.2.2.1) guards.2.2.2.2

end InitECandidate.Solver.Headers.CurrentDecode

#print axioms InitECandidate.Solver.Headers.CurrentDecode.after_kind_cost
