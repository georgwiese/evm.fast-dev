import InitECandidate.Solver.Mpt.WitnessDecodeValueCost
import InitECandidate.Solver.Mpt.CompactToNibblesSnapshotCall

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Price the actual original compact caller and its selected leaf/record
suffix. Its fresh output preserves the current physical row array, so the
value parser's real words and bounded input extent remain available. -/
theorem compact_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array listPointer itemPointer header payload flag heap cursor limit : BitVec 64)
    (bytes : Nat) (items : List Rlp.ListItem) (valueItem : Rlp.ListItem)
    (rows : Rows source array listPointer bytes items) (selected : items[1]?=some valueItem)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pathCell : source.locals.lookup (ofString "pi")=some (Rlp.Item.result itemPointer header payload flag))
    (payloadBound : payload.toNat≤bytes) (small : bytes≤1024)
    (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source compactCall).2.clock≤bytes/4+60*bytes+52 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [field "pi" 1,field "pi" 2]=
      some [.val (.word (itemPointer+header)),.val (.word (BitVec.ofNat 64 payload.toNat))]:=by
    simp [field,evalListHOLFinite,evalListHOLExact,evalHOLExact,QueryBranch.localVar,toExact,pathCell,Rlp.Item.result]
  have price:=CompactToNibbles.scoped_snapshot_cost source (itemPointer+header) heap cursor limit payload.toNat (by omega)
    "cn" [field "pi" 1,field "pi" 2] afterCompact (60*bytes+45) args heapCell heapArena heapAligned arena installed (by
      intro target nibbles leaf snapshot
      let ready:=Input.CallNormal.continuationEntry source target "cn" (CompactToNibbles.output heap nibbles leaf)
      have domain:=congrArg PanSemStateFiniteExact.memaddrs snapshot.metadata
      change target.memaddrs=source.memaddrs at domain
      have codeEq:=congrArg PanSemStateFiniteExact.code snapshot.metadata
      change target.code=source.code at codeEq
      have currentRows : Rows ready array listPointer bytes items:=rows.earlier source ready array listPointer bytes items heap.toNat beforeArray domain
        (fun query before=>snapshot.memory query (Or.inl before))
      have currentArena:=Rlp.Validation.Arena.of_fields target ready cursor limit snapshot.arena rfl rfl
      have currentArray : ready.locals.lookup (ofString "arr")=some (.val (.word array)):=
        (Input.CallNormal.continuation_lookup_other source target "cn" "arr" _ (by decide)).trans arrayCell
      have currentCompact : ready.locals.lookup (ofString "cn")=some (CompactToNibbles.output heap nibbles leaf):=
        Input.CallNormal.continuation_lookup_same _ _ _ _
      have currentInstalled : Input.OriginalCode.Installed ready.code:=by
        change Input.OriginalCode.Installed target.code
        rw [codeEq]
        exact installed
      exact after_compact_cost ready array listPointer cursor limit heap (BitVec.ofNat 64 nibbles) leaf bytes items valueItem currentRows selected currentArray currentCompact currentArena currentInstalled)
  rw [compact_shape]
  exact price.trans (by omega)

theorem after_path_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array listPointer itemPointer header payload flag heap cursor limit : BitVec 64)
    (bytes : Nat) (items : List Rlp.ListItem) (valueItem : Rlp.ListItem)
    (rows : Rows source array listPointer bytes items) (selected : items[1]?=some valueItem)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pathCell : source.locals.lookup (ofString "pi")=some (Rlp.Item.result itemPointer header payload flag))
    (payloadBound : payload.toNat≤bytes) (small : bytes≤1024)
    (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterPath).2.clock≤bytes/4+60*bytes+52 := by
  have compactPrice:=compact_call_cost source array listPointer itemPointer header payload flag heap cursor limit bytes items valueItem rows selected
    arrayCell pathCell payloadBound small beforeArray heapCell heapArena heapAligned arena installed
  have total:=Fail.guard_reached_cost source (.cmp .notEqual (field "pi" 0) (.const 0#64)) 5#64 compactCall (bytes/4+60*bytes+52) installed (fun _=>compactPrice)
  rw [after_path_shape]
  exact total.trans (by omega)

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.compact_call_cost
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.after_path_cost
