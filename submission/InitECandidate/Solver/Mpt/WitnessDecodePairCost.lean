import InitECandidate.Solver.Mpt.WitnessDecodeCompactCost
import InitECandidate.Solver.Rlp.ItemFrameTrace

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Complete original two-item path: real path parser, compact conversion,
leaf/value parser or extension record. The current physical row array and
heap/scratch geometry supply every reached helper premise. -/
theorem pair_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array listPointer heap cursor limit : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem)
    (pathItem valueItem : Rlp.ListItem) (rows : Rows source array listPointer bytes items)
    (pathSelected : items[0]?=some pathItem) (valueSelected : items[1]?=some valueItem)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (small : bytes≤1024) (scratchBelow : cursor.toNat≤array.toNat)
    (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source pairBody).2.clock≤bytes/4+120*bytes+94 := by
  obtain ⟨args,positive,pathBound,lower,upper⟩:=rows.arguments source array listPointer bytes 0 items pathItem pathSelected arrayCell
  have fits : (Rlp.Slices.itemPointer listPointer items 0).toNat+pathItem.total.toNat<2^64:=upper.trans_lt rows.fits
  have price:=Rlp.Item.scoped_frame_cost source (Rlp.Slices.itemPointer listPointer items 0) pathItem.total cursor limit "pi" (recordArguments 0) afterPath
    (bytes/4+60*bytes+52) args arena fits installed (by
      intro target header payload flag valid nextArena above domain endian codeEq heapEq
      let ready:=Input.CallNormal.continuationEntry source target "pi" (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 0) header payload flag)
      have currentRows : Rows ready array listPointer bytes items:=rows.above source ready array listPointer bytes items cursor.toNat scratchBelow domain above
      have currentArray : ready.locals.lookup (ofString "arr")=some (.val (.word array)):=
        (Input.CallNormal.continuation_lookup_other source target "pi" "arr" _ (by decide)).trans arrayCell
      have pathCell : ready.locals.lookup (ofString "pi")=some (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 0) header payload flag):=
        Input.CallNormal.continuation_lookup_same _ _ _ _
      have currentArena:=Rlp.Validation.Arena.of_fields target ready cursor limit nextArena rfl rfl
      have currentHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=heapEq.trans heapCell
      have currentInstalled : Input.OriginalCode.Installed ready.code:=by
        change Input.OriginalCode.Installed target.code
        rw [codeEq]
        exact installed
      have actualFields:=Rlp.Item.Valid.result_fields (Rlp.Slices.itemPointer listPointer items 0) header payload flag pathItem.total.toNat valid
      exact after_path_cost ready array listPointer (Rlp.Slices.itemPointer listPointer items 0) header payload flag heap cursor limit bytes items valueItem currentRows valueSelected
        currentArray pathCell (by omega) small beforeArray currentHeap heapArena heapAligned currentArena currentInstalled)
  rw [path_shape]
  exact price.trans (by omega)

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.pair_cost
