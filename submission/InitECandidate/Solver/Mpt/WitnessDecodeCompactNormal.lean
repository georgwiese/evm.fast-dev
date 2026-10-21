import InitECandidate.Solver.Mpt.WitnessDecodeRows
import InitECandidate.Solver.Mpt.CompactToNibblesSnapshotNormal
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A genuine original compact caller return preserves the physical row
array and exposes the actual bounded nibble buffer/leaf flag at the true
leaf-versus-extension suffix. Every allocation/frame fact is derived. -/
theorem compact_normal_entry (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array listPointer itemPointer header payload heap cursor limit : BitVec 64)
    (bytes : Nat) (items : List Rlp.ListItem)
    (rows : Rows source array listPointer bytes items)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pathCell : source.locals.lookup (ofString "pi")=some (Rlp.Item.result itemPointer header payload 0#64))
    (payloadBound : payload.toNat≤bytes) (small : bytes≤1024)
    (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source compactCall=(some (.returned value),post)) :
    ∃ target nibbles leaf inner,
      let ready:=Input.CallNormal.continuationEntry source target "cn" (CompactToNibbles.output heap nibbles leaf)
      CompactToNibbles.Snapshot source ready payload.toNat heap cursor limit nibbles leaf ∧
      Rows ready array listPointer bytes items ∧ Input.OriginalCode.Installed ready.code ∧
      ready.locals.lookup (ofString "arr")=some (.val (.word array)) ∧
      ready.locals.lookup (ofString "cn")=some (CompactToNibbles.output heap nibbles leaf) ∧
      evaluateHOLFiniteState ready afterCompact=(some (.returned value),inner) ∧ post=QueryBranch.restore source "cn" inner := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [field "pi" 1,field "pi" 2]=
      some [.val (.word (itemPointer+header)),.val (.word (BitVec.ofNat 64 payload.toNat))]:=by
    simp [field,evalListHOLFinite,evalListHOLExact,evalHOLExact,QueryBranch.localVar,toExact,pathCell,Rlp.Item.result]
  rw [compact_shape] at normal
  obtain ⟨funded,target,nibbles,leaf,inner,snapshot,continued,endpoint⟩:=CompactToNibbles.scoped_snapshot_normal source post (itemPointer+header) heap cursor limit payload.toNat (by omega)
    "cn" [field "pi" 1,field "pi" 2] afterCompact args heapCell heapArena heapAligned arena installed value normal
  let ready:=Input.CallNormal.continuationEntry source target "cn" (CompactToNibbles.output heap nibbles leaf)
  have physical:=snapshot.resumed source target payload.toNat heap cursor limit nibbles leaf "cn"
  have domain:=congrArg PanSemStateFiniteExact.memaddrs physical.metadata
  change ready.memaddrs=source.memaddrs at domain
  have codeEq:=congrArg PanSemStateFiniteExact.code physical.metadata
  change ready.code=source.code at codeEq
  have currentRows : Rows ready array listPointer bytes items:=rows.earlier source ready array listPointer bytes items heap.toNat beforeArray domain
    (fun query before=>physical.memory query (Or.inl before))
  have currentInstalled : Input.OriginalCode.Installed ready.code:=by rw [codeEq]; exact installed
  have currentArray : ready.locals.lookup (ofString "arr")=some (.val (.word array)):=
    (Input.CallNormal.continuation_lookup_other source target "cn" "arr" _ (by decide)).trans arrayCell
  have compactCell : ready.locals.lookup (ofString "cn")=some (CompactToNibbles.output heap nibbles leaf):=
    Input.CallNormal.continuation_lookup_same _ _ _ _
  exact ⟨target,nibbles,leaf,inner,physical,currentRows,currentInstalled,currentArray,compactCell,continued,endpoint⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.compact_normal_entry
