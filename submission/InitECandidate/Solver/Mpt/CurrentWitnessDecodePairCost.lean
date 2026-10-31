import InitECandidate.Solver.Mpt.CurrentWitnessDecodeLeaf
import InitECandidate.Solver.Input.ConditionalNone
import InitECandidate.Solver.Mpt.CompactToNibblesCurrentSnapshot
import InitECandidate.Solver.Input.ClockCostSequenceReached
import InitECandidate.Solver.Input.ClockCostCurrentConditional

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem current_after_compact_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (selected : items[1]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (arena : Rlp.LiveArena source) :
    source.clock-(evaluateHOLFiniteState source afterCompact).2.clock≤60*bytes+17 := by
  have front:=ClockCost.conditional_current source (.cmp .notEqual (field "cn" 2) (.const 0#64)) leafBody .skip (60*bytes+15) 0
    (current_leaf_price source array pointer bytes items item rows selected arrayCell arena) (ClockCost.skip source.code source rfl)
  simp only [Nat.max_zero] at front
  rw [after_compact_shape]
  exact ClockCost.sequence_reached_current source _ extensionBody (60*bytes+15) 2 front (by
    intro middle normal
    have same : middle=source := by
      rcases conditional_none source middle _ leafBody .skip normal with yes|no
      · exact (leaf_body_no_fallthrough source (congrArg Prod.fst yes)).elim
      · rw [evaluateHOLFiniteState_skip] at no
        exact (congrArg Prod.snd no).symm
    subst middle
    exact suspended_extension_price source.code arena.code source rfl)

theorem current_compact_call_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer itemPointer header payload flag heap : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (selected : items[1]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pathCell : source.locals.lookup (ofString "pi")=some (Rlp.Item.result itemPointer header payload flag))
    (payloadBound : payload.toNat≤bytes) (small : bytes≤1024)
    (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : Rlp.LiveArena source) :
    source.clock-(evaluateHOLFiniteState source compactCall).2.clock≤bytes/4+60*bytes+24 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [field "pi" 1,field "pi" 2]=
      some [.val (.word (itemPointer+header)),.val (.word (BitVec.ofNat 64 payload.toNat))] := by
    simp [field,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pathCell,Rlp.Item.result]
  rw [compact_shape]
  have price:=CompactToNibbles.scoped_current_cost source (itemPointer+header) heap payload.toNat (by omega) "cn" [field "pi" 1,field "pi" 2] afterCompact
    (60*bytes+17) args heapCell heapArena heapBound aligned arena (by
      intro target nibbles leaf snapshot
      let ready:=CallNormal.continuationEntry source target "cn" (CompactToNibbles.output heap nibbles leaf)
      have domain:=congrArg PanSemStateFiniteExact.memaddrs snapshot.metadata
      change target.memaddrs=source.memaddrs at domain
      have currentRows : Rows ready array pointer bytes items := rows.earlier source ready array pointer bytes items heap.toNat beforeArray domain
        (fun query before=>snapshot.memory query (Or.inl before))
      have currentArray : ready.locals.lookup (ofString "arr")=some (.val (.word array)) :=
        (CallNormal.continuation_lookup_other source target "cn" "arr" _ (by decide)).trans arrayCell
      exact current_after_compact_price ready array pointer bytes items item currentRows selected currentArray (snapshot.arena.of_frame rfl))
  have lengthPrice : payload.toNat/4≤bytes/4 := Nat.div_le_div_right payloadBound
  exact Nat.le_trans price (by omega)

theorem current_after_path_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer itemPointer header payload flag heap : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (selected : items[1]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pathCell : source.locals.lookup (ofString "pi")=some (Rlp.Item.result itemPointer header payload flag))
    (payloadBound : payload.toNat≤bytes) (small : bytes≤1024)
    (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : Rlp.LiveArena source) :
    source.clock-(evaluateHOLFiniteState source afterPath).2.clock≤bytes/4+60*bytes+24 := by
  rw [after_path_shape]
  have price:=Fail.guard_reached_cost source (.cmp .notEqual (field "pi" 0) (.const 0#64)) 5#64 compactCall (bytes/4+60*bytes+24) arena.code (fun _=>
    current_compact_call_price source array pointer itemPointer header payload flag heap bytes items item rows selected arrayCell pathCell payloadBound small beforeArray heapCell heapArena heapBound aligned arena)
  exact Nat.le_trans price (by omega)

/-- The real two-item path shares the same validated byte extent across its
two RLP calls. Fresh compact output preserves the actual second row. -/
theorem current_pair_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer heap : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (first second : Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (firstSelected : items[0]?=some first) (secondSelected : items[1]?=some second)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (small : bytes≤1024) (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : Rlp.LiveArena source) :
    source.clock-(evaluateHOLFiniteState source pairBody).2.clock≤bytes/4+120*bytes+35 := by
  obtain ⟨args,positive,firstBound,lower,upper⟩:=rows.arguments source array pointer bytes 0 items first firstSelected arrayCell
  have fits : (Rlp.Slices.itemPointer pointer items 0).toNat+first.total.toNat<2^64 := by have h:=rows.fits; omega
  rw [path_shape]
  have price:=Rlp.CurrentItem.scoped_valid_cost source (Rlp.Slices.itemPointer pointer items 0) first.total arena fits "pi" (recordArguments 0) afterPath
    (bytes/4+60*bytes+24) args (by
      intro current answer valid frame
      obtain ⟨header,payload,flag,valueEq,headerBound,positive,extent,binary,listHeader⟩:=valid
      subst answer
      let ready:=setVarHOLFinite (ofString "pi") (Rlp.Item.result (Rlp.Slices.itemPointer pointer items 0) header payload flag) {current with locals:=source.locals}
      have currentRows : Rows ready array pointer bytes items := rows.earlier source ready array pointer bytes items 2952790016
        (by omega) (MemoryMetadata.domain frame.metadata)
        (fun query before=>frame.outside query (Or.inl before))
      have globals := congrArg PanSemStateFiniteExact.globals frame.metadata
      change current.globals=source.globals at globals
      have currentHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) := by
        change current.globals.lookup (ofString "heap_ptr")=_
        rw [globals]
        exact heapCell
      have currentArena : Rlp.LiveArena ready:=arena.of_metadata frame.metadata
      have currentArray : ready.locals.lookup (ofString "arr")=some (.val (.word array)) := by
        simpa [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "pi"≠ofString "arr" from by decide] using arrayCell
      have pathCell : ready.locals.lookup (ofString "pi")=some (Rlp.Item.result (Rlp.Slices.itemPointer pointer items 0) header payload flag) := by
        simp [ready,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
      exact current_after_path_price ready array pointer _ header payload flag heap bytes items second currentRows secondSelected currentArray pathCell
        (by omega) small beforeArray currentHeap heapArena heapBound aligned currentArena)
  omega

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_compact_call_price
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_pair_price
