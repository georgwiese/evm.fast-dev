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
    (small : bytes≤1024) (scratchBelow : cursor.toNat≤array.toNat)
    (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source pairBody=(some (.returned value),post)) :
    ∃ pathTarget header payload compactTarget nibbles leaf inner,
      let parsed:=Input.CallNormal.continuationEntry source pathTarget "pi" (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 0) header payload 0#64)
      let ready:=Input.CallNormal.continuationEntry parsed compactTarget "cn" (CompactToNibbles.output heap nibbles leaf)
      payload.toNat≤bytes ∧ Rlp.Validation.Above source parsed cursor.toNat ∧
      parsed.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr") ∧
      parsed.memaddrs=source.memaddrs ∧ parsed.be=source.be ∧ parsed.code=source.code ∧
      (∀ key,parsed.globals.lookup key=source.globals.lookup key) ∧
      CompactToNibbles.Snapshot parsed ready payload.toNat heap cursor limit nibbles leaf ∧
      Rows ready array listPointer bytes items ∧ Input.OriginalCode.Installed ready.code ∧
      (∀ name : String,ofString "pi"≠ofString name → ofString "cn"≠ofString name → ready.locals.lookup (ofString name)=source.locals.lookup (ofString name)) ∧
      ready.locals.lookup (ofString "arr")=some (.val (.word array)) ∧
      ready.locals.lookup (ofString "cn")=some (CompactToNibbles.output heap nibbles leaf) ∧
      evaluateHOLFiniteState ready afterCompact=(some (.returned value),inner) ∧ post=restore source "pi" (restore parsed "cn" inner) := by
  obtain ⟨pathTarget,header,payload,middle,valid,payloadBound,pathRows,pathArena,above,codeEq,heapEq,pathDomain,pathEndian,pathGlobals,pathArray,pathCell,compactRun,pathEndpoint⟩:=
    path_normal source post array listPointer cursor limit bytes items pathItem rows selected arrayCell scratchBelow arena installed value normal
  let parsed:=Input.CallNormal.continuationEntry source pathTarget "pi" (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 0) header payload 0#64)
  have parsedInstalled : Input.OriginalCode.Installed parsed.code:=by rw [codeEq]; exact installed
  have parsedHeap : parsed.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=heapEq.trans heapCell
  obtain ⟨compactTarget,nibbles,leaf,inner,snapshot,currentRows,currentInstalled,currentArray,currentCompact,continued,compactEndpoint⟩:=
    compact_normal_entry parsed middle array listPointer (Rlp.Slices.itemPointer listPointer items 0) header payload heap cursor limit bytes items pathRows pathArray pathCell
      payloadBound small beforeArray parsedHeap heapArena heapAligned pathArena parsedInstalled value compactRun
  let ready:=Input.CallNormal.continuationEntry parsed compactTarget "cn" (CompactToNibbles.output heap nibbles leaf)
  have retained (name : String) (notPath : ofString "pi"≠ofString name) (notCompact : ofString "cn"≠ofString name) :
      ready.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    (Input.CallNormal.continuation_lookup_other parsed compactTarget "cn" name _ notCompact).trans
      (Input.CallNormal.continuation_lookup_other source pathTarget "pi" name _ notPath)
  exact ⟨pathTarget,header,payload,compactTarget,nibbles,leaf,inner,payloadBound,above,heapEq,pathDomain,pathEndian,codeEq,pathGlobals,snapshot,currentRows,currentInstalled,retained,currentArray,currentCompact,continued,
    by rw [pathEndpoint,compactEndpoint]⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.pair_prefix_normal
