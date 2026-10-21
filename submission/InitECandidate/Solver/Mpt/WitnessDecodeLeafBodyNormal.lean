import InitECandidate.Solver.Mpt.WitnessDecodeValueNormal
import InitECandidate.Solver.Mpt.WitnessDecodeLeafView
import InitECandidate.Solver.Mpt.WitnessDecodeAllocationFrame

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The complete original leaf branch derives its actual row1 string,
fresh node and physical path/value/parent views. The value parser and node
allocation belong to the same returning execution; no future successful
parse, allocation or initialized output is assumed. -/
theorem leaf_body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db array pointer length listPointer nibbles nibbleLength leaf heap cursor limit : BitVec 64)
    (bytes : Nat) (items : List Rlp.ListItem) (valueItem : Rlp.ListItem)
    (rows : Rows source array listPointer bytes items) (selected : items[1]?=some valueItem)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (compactCell : source.locals.lookup (ofString "cn")=some (.rStruct [.val (.word nibbles),.val (.word nibbleLength),.val (.word leaf)]))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (scratchBelow : cursor.toNat≤array.toNat)
    (heapLower : 2713731432≤heap.toNat) (dbBefore : db.toNat≤heap.toNat)
    (parentBound : length.toNat≤1024) (parentLower : 2713731432≤pointer.toNat)
    (parentBefore : pointer.toNat+length.toNat≤db.toNat)
    (payloadLower : pointer.toNat≤listPointer.toNat) (payloadUpper : listPointer.toNat+bytes≤pointer.toNat+length.toNat)
    (nibbleArena : AllocatedBytes.Arena nibbles nibbleLength.toNat) (nibbleBound : nibbleLength.toNat≤2048)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source leafBody=(some (.returned value),post)) :
    value=.rStruct [.val (.word 0#64),.val (.word heap)] ∧ NormalFrame source post heap cursor limit ∧
      Rlp.Validation.Arena post cursor limit ∧
      (∃ valuePointer valueLength,LeafView post heap db pointer length nibbles nibbleLength valuePointer valueLength) ∧
      ∃ finalHeap,post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat+64≤finalHeap.toNat := by
  obtain ⟨target,header,payload,inner,valid,valueBound,currentRows,currentArena,above,codeEq,heapEq,domain,endian,globalCells,currentArray,currentValue,continued,endpoint⟩:=
    value_normal source post array listPointer cursor limit bytes items valueItem rows selected arrayCell scratchBelow arena installed value normal
  let ready:=Input.CallNormal.continuationEntry source target "vi" (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 1) header payload 0#64)
  have currentPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)):=
    (Input.CallNormal.continuation_lookup_other source target "vi" "p" _ (by decide)).trans pointerCell
  have currentLength : ready.locals.lookup (ofString "n")=some (.val (.word length)):=
    (Input.CallNormal.continuation_lookup_other source target "vi" "n" _ (by decide)).trans lengthCell
  have currentCompact : ready.locals.lookup (ofString "cn")=some (.rStruct [.val (.word nibbles),.val (.word nibbleLength),.val (.word leaf)]):=
    (Input.CallNormal.continuation_lookup_other source target "vi" "cn" _ (by decide)).trans compactCell
  have currentHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=heapEq.trans heapCell
  have currentInstalled : Input.OriginalCode.Installed ready.code:=by rw [codeEq]; exact installed
  obtain ⟨nodeArena,nextArena,valueEq,funding,postEq⟩:=leaf_allocation_normal ready inner pointer length nibbles nibbleLength leaf 0#64
    (Rlp.Slices.itemPointer listPointer items 1+header) payload (header+payload) heap cursor limit currentPointer currentLength currentCompact currentValue
    currentHeap heapArena heapAligned currentArena currentInstalled value continued
  have allocationFrame:=leaf_frame_of_post ready inner heap cursor limit (leafWords nibbles nibbleLength (Rlp.Slices.itemPointer listPointer items 1+header) payload)
    (leafParentWords pointer length) nodeArena heapAligned nextArena postEq
  have prefixed:=allocationFrame.prefix source ready inner heap cursor limit domain endian codeEq globalCells above
  have frame : NormalFrame source post heap cursor limit:=prefixed.of_erase source post inner heap cursor limit (by rw [endpoint]; rfl)
  obtain ⟨itemPositive,itemBound,itemLower,itemUpper⟩:=rows.intervals 1 valueItem selected
  have fields:=Rlp.Item.Valid.result_fields (Rlp.Slices.itemPointer listPointer items 1) header payload 0#64 valueItem.total.toNat valid
  have number : (Rlp.Slices.itemPointer listPointer items 1+header).toNat=(Rlp.Slices.itemPointer listPointer items 1).toNat+header.toNat:=
    BitVec.toNat_add_of_lt (by have fits:=rows.fits; omega)
  have valueLower : 2713731432≤(Rlp.Slices.itemPointer listPointer items 1+header).toNat:=by rw [number]; omega
  have valueBefore : (Rlp.Slices.itemPointer listPointer items 1+header).toNat+payload.toNat≤db.toNat:=by rw [number]; omega
  have parentArena : AllocatedBytes.Arena pointer length.toNat:=⟨by omega,by have upper:=heapArena.upper; omega⟩
  have payloadArena : AllocatedBytes.Arena (Rlp.Slices.itemPointer listPointer items 1+header) payload.toNat:=⟨by omega,by have upper:=heapArena.upper; omega⟩
  have view:=leaf_view_of_post ready inner heap db pointer length nibbles nibbleLength (Rlp.Slices.itemPointer listPointer items 1+header) payload
    currentArena.domain nodeArena heapAligned heapLower parentArena parentBound parentLower parentBefore nibbleArena nibbleBound payloadArena (by omega) valueLower valueBefore postEq
  have finalView : LeafView post heap db pointer length nibbles nibbleLength (Rlp.Slices.itemPointer listPointer items 1+header) payload:=by
    apply view.of_fields post
    · rw [endpoint]; rfl
    · rw [endpoint]; rfl
  have finalArena : Rlp.Validation.Arena post cursor limit:=by
    apply nextArena.of_fields inner post cursor limit
    · rw [endpoint]; rfl
    · rw [endpoint]; rfl
  have globals:=congrArg PanSemStateFiniteExact.globals postEq
  change inner.globals=(PersistentAlloc.post ready heap 64#64).globals at globals
  have finalHeap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 64#64))):=by
    rw [endpoint]
    change inner.globals.lookup (ofString "heap_ptr")=_
    rw [globals]
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
  have checked:=PersistentAlloc.guards heap 64#64 nodeArena.upper
  have grows : heap.toNat+64≤(PersistentAlloc.rounded heap 64#64).toNat:=checked.2.2.1
  have finalHeapArena : AllocatedBytes.Arena (PersistentAlloc.rounded heap 64#64) 0:=
    ⟨by have lower:=nodeArena.lower; omega,by have upper:=checked.2.2.2.1; omega⟩
  exact ⟨valueEq,frame,finalArena,⟨_,payload,finalView⟩,_,finalHeap,finalHeapArena,checked.2.2.2.2,grows⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.leaf_body_normal
