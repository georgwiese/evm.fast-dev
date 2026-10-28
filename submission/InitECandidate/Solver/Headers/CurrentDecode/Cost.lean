import InitECandidate.Solver.Headers.CurrentDecode.AfterTopCost
import InitECandidate.Solver.Rlp.CurrentDecodeCall

namespace InitECandidate.Solver.Headers.CurrentDecode
open Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 10000

/-- Complete unchanged current decode_header208, from actual input and heap
geometry. All parser, count, allocation, guard, helper/store and stopped paths
are included; no future parser result or allocation room is assumed. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (before : pointer.toNat+length.toNat≤heap.toNat) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤195*length.toNat+473 := by
  have fits : pointer.toNat+length.toNat<2^64 := by have h:=heap.isLt; omega
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) topArguments=some (Rlp.Header.values pointer length) := by
    simp [topArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  rw [body_shape]
  have actual:=Rlp.CurrentDecode.scoped_valid_cost source pointer length arena fits "top" topArguments afterTop (149*length.toNat+460) args ?_
  · have arithmetic : ∀ n : Nat,46*n+(149*n+460)+13≤195*n+473 := by intro n; omega
    exact Nat.le_trans actual (arithmetic length.toNat)
  · intro answer clock complete
    obtain ⟨header,payload,flag,same,small,positive,extent,binary,listHeader⟩:=complete
    subst answer
    let ready:=setVarHOLFinite (ofString "top") (Rlp.Item.result pointer header payload flag) {source with clock:=clock}
    have topCell : ready.locals.lookup (ofString "top")=some (Rlp.Item.result pointer header payload flag) := by
      simp [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    have number : (pointer+header).toNat=pointer.toNat+header.toNat := BitVec.toNat_add_of_lt (by omega)
    have price:=after_top_cost ready pointer header payload flag heap topCell (arena.of_frame rfl) heapGlobal heapBound heapLower heapAligned (by rw [number]; omega)
    change clock-(evaluateHOLFiniteState ready afterTop).2.clock≤_ at price ⊢
    omega

/-- The real ordinary header caller adds exactly one source-call allowance. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap : BitVec 64) (arena : CurrentStartup.ArenaState source)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤2952790016) (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (before : pointer.toNat+length.toNat≤heap.toNat)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (Rlp.Header.values pointer length)) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "decode_header") expressions)).2.clock≤195*length.toNat+474 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "decode_header") body .one pointer length (original_code source.code arena.code)
  have price:=body_cost (callEntryStateHOLFinite source callee) pointer length heap pointerLocal lengthLocal (arena.of_frame rfl) heapGlobal heapBound heapLower heapAligned before
  exact ClockCost.call_current source destination (ofString "decode_header") expressions (Rlp.Header.values pointer length) body callee .one (195*length.toNat+473) args called price

end InitECandidate.Solver.Headers.CurrentDecode

#print axioms InitECandidate.Solver.Headers.CurrentDecode.body_cost
#print axioms InitECandidate.Solver.Headers.CurrentDecode.call_cost
