import InitECandidate.Solver.Mpt.WitnessDecodePathNormal
import InitECandidate.Solver.Mpt.WitnessDecodeCompactNormal

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine original two-item return reaches the actual leaf/extension
decision after the real path parser and compact allocation. Physical rows,
nibble ownership, restored scratch and caller bindings all refer to the
same current state; both original saved scopes are retained exactly. -/
theorem pair_prefix_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array listPointer heap cursor limit : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (pathItem : Rlp.ListItem)
    (rows : Rows source array listPointer bytes items) (selected : items[0]?=some pathItem)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (small : bytes≤1024)
    (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source pairBody=(some (.returned value),post)) :
    ∃ pathTarget header payload compactTarget nibbles leaf inner,
      let parsed:=Input.CallNormal.continuationEntry source pathTarget "pi" (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 0) header payload 0#64)
      let ready:=Input.CallNormal.continuationEntry parsed compactTarget "cn" (CompactToNibbles.output heap nibbles leaf)
      payload.toNat≤bytes ∧
      CompactToNibbles.CurrentSnapshot parsed ready payload.toNat heap nibbles leaf ∧
      Rows ready array listPointer bytes items ∧ Rlp.Validation.Arena ready cursor limit ∧
      LiveFrame source ready heap cursor limit ∧
      (∀ name : String,ofString "pi"≠ofString name → ofString "cn"≠ofString name → ready.locals.lookup (ofString name)=source.locals.lookup (ofString name)) ∧
      ready.locals.lookup (ofString "arr")=some (.val (.word array)) ∧
      ready.locals.lookup (ofString "cn")=some (CompactToNibbles.output heap nibbles leaf) ∧
      evaluateHOLFiniteState ready afterCompact=(some (.returned value),inner) ∧ post=restore source "pi" (restore parsed "cn" inner) := by
  obtain ⟨pathTarget,header,payload,middle,valid,payloadBound,pathRows,pathArena,pure,pathArray,pathCell,compactRun,pathEndpoint⟩:=
    path_normal source post array listPointer cursor limit bytes items pathItem rows selected arrayCell live arena value normal
  let parsed:=Input.CallNormal.continuationEntry source pathTarget "pi" (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 0) header payload 0#64)
  have parsedLive : Rlp.LiveArena parsed:=live.of_frame pure
  have globals:=congrArg PanSemStateFiniteExact.globals pure
  change parsed.globals=source.globals at globals
  have parsedHeap : parsed.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
  obtain ⟨compactTarget,nibbles,leaf,inner,snapshot,currentRows,currentArena,currentArray,currentCompact,continued,compactEndpoint⟩:=
    compact_normal_entry parsed middle array listPointer (Rlp.Slices.itemPointer listPointer items 0) header payload heap cursor limit bytes items pathRows pathArray pathCell
      payloadBound small beforeArray parsedHeap heapArena heapBound heapAligned parsedLive pathArena value compactRun
  let ready:=Input.CallNormal.continuationEntry parsed compactTarget "cn" (CompactToNibbles.output heap nibbles leaf)
  have compactFrame:=snapshot.live_frame parsedLive pathArena
  have frame:=LiveFrame.of_erase parsed ready source ready heap cursor limit compactFrame pure.symm rfl
  have retained (name : String) (notPath : ofString "pi"≠ofString name) (notCompact : ofString "cn"≠ofString name) :
      ready.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    (Input.CallNormal.continuation_lookup_other parsed compactTarget "cn" name _ notCompact).trans
      (Input.CallNormal.continuation_lookup_other source pathTarget "pi" name _ notPath)
  exact ⟨pathTarget,header,payload,compactTarget,nibbles,leaf,inner,payloadBound,snapshot,currentRows,currentArena,frame,retained,currentArray,currentCompact,continued,
    by rw [pathEndpoint,compactEndpoint]⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.pair_prefix_normal
