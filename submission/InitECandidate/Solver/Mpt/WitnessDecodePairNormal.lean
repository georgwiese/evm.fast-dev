import InitECandidate.Solver.Mpt.WitnessDecodePairPrefixNormal
import InitECandidate.Solver.Mpt.WitnessDecodeLeafBodyNormal
import InitECandidate.Solver.Mpt.WitnessDecodeExtensionView
import InitECandidate.Solver.Mpt.WitnessDecodeSnapshotFrame
import InitECandidate.Solver.Mpt.WitnessDecodeControl
import InitECandidate.Solver.Mpt.WitnessRecordFrame

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete original two-item decode normal contract. The same actual
path/compact/value/allocation execution returns either the physical leaf or
the real initialized extension record. Heap/scratch frames and record
allowance progress are derived, including both caller-scope restorations. -/
theorem pair_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db array pointer length listPointer heap cursor limit : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem)
    (rows : Rows source array listPointer bytes items) (count : items.length=2)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (below : cursor.toNat≤2713717616)
    (arrayFloor : 2713731432≤array.toNat) (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (heapLower : 2713731432≤heap.toNat) (dbBefore : db.toNat≤heap.toNat)
    (parentBound : length.toNat≤1024) (parentLower : 2713731432≤pointer.toNat)
    (parentBefore : pointer.toNat+length.toNat≤db.toNat)
    (payloadLower : pointer.toNat≤listPointer.toNat) (payloadUpper : listPointer.toNat+bytes≤pointer.toNat+length.toNat)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source pairBody=(some (.returned value),post)) :
    NormalFrame source post heap cursor limit ∧ ∃ nibbleLength : BitVec 64,
      (∃ node valuePointer valueLength,value=.rStruct [.val (.word 0#64),.val (.word node)] ∧
        LeafView post node db pointer length heap nibbleLength valuePointer valueLength ∧ heap.toNat≤node.toNat ∧
        Rlp.Validation.Arena post cursor limit ∧
        ∃ finalHeap,post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
          AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ node.toNat+64≤finalHeap.toNat) ∨
      (∃ next,
        let data:=extensionDescription array pointer length listPointer bytes items heap nibbleLength
        value=.rStruct [.val (.word 1#64),.val (.word (WitnessRecord.pointer cursor))] ∧
        WitnessRecord.View post (WitnessRecord.pointer cursor) db data ∧ data.BeforeHeap next.toNat ∧
        post.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) ∧ AllocatedBytes.Arena next 0 ∧ next.toNat%8=0 ∧ heap.toNat≤next.toNat ∧
        Rlp.Validation.Arena post (WitnessRecord.pointer cursor) limit ∧
        ((WitnessRecord.pointer cursor).toNat-limit.toNat)/88+1≤(cursor.toNat-limit.toNat)/88) := by
  have firstInside : 0<items.length:=by omega
  let pathItem:=items[0]
  have pathSelected : items[0]?=some pathItem:=by simp [pathItem,firstInside]
  have small : bytes≤1024:=by omega
  have scratchBelow : cursor.toNat≤array.toNat:=by omega
  obtain ⟨pathTarget,header,payload,compactTarget,nibbles,leaf,inner,payloadBound,pathAbove,pathHeap,pathDomain,pathEndian,pathCode,pathGlobals,snapshot,currentRows,currentInstalled,retained,currentArray,currentCompact,continued,endpoint⟩:=
    pair_prefix_normal source post array listPointer heap cursor limit bytes items pathItem rows pathSelected arrayCell small scratchBelow beforeArray heapCell heapArena heapAligned arena installed value normal
  let parsed:=Input.CallNormal.continuationEntry source pathTarget "pi" (Rlp.Item.result (Rlp.Slices.itemPointer listPointer items 0) header payload 0#64)
  let ready:=Input.CallNormal.continuationEntry parsed compactTarget "cn" (CompactToNibbles.output heap nibbles leaf)
  let next:=PersistentAlloc.rounded heap (BitVec.ofNat 64 (2*payload.toNat))
  have allocatedGrowth : heap.toNat+2*payload.toNat≤next.toNat:=snapshot.grows
  have grows : heap.toNat≤next.toNat:=by omega
  have nibbleBound : nibbles≤2048:=by have bound:=snapshot.nibbleBound; omega
  have nibbleNumber : (BitVec.ofNat 64 nibbles).toNat=nibbles:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have nibbleArena : AllocatedBytes.Arena heap (BitVec.ofNat 64 nibbles).toNat:=by
    rw [nibbleNumber]
    exact snapshot.outputArena.weaken heap (2*payload.toNat) nibbles snapshot.nibbleBound
  have compactFrame : NormalFrame source ready heap cursor limit:=
    (compact_snapshot_frame parsed ready payload.toNat heap cursor limit nibbles leaf snapshot).prefix source parsed ready heap cursor limit pathDomain pathEndian pathCode pathGlobals pathAbove
  have currentPointer : ready.locals.lookup (ofString "p")=some (.val (.word pointer)):=(retained "p" (by decide) (by decide)).trans pointerCell
  have currentLength : ready.locals.lookup (ofString "n")=some (.val (.word length)):=(retained "n" (by decide) (by decide)).trans lengthCell
  rw [compact_choice ready heap (BitVec.ofNat 64 nibbles) leaf currentCompact] at continued
  by_cases isLeaf : leaf≠0#64
  · rw [if_pos isLeaf] at continued
    have valueInside : 1<items.length:=by omega
    let valueItem:=items[1]
    have valueSelected : items[1]?=some valueItem:=by simp [valueItem,valueInside]
    obtain ⟨valueEq,leafFrame,leafArena,⟨valuePointer,valueLength,leafView⟩,finalHeap,finalHeapCell,finalHeapArena,finalHeapAligned,nodeBefore⟩:=
      leaf_body_normal ready inner db array pointer length listPointer heap (BitVec.ofNat 64 nibbles) leaf next cursor limit bytes items valueItem currentRows valueSelected currentArray currentPointer currentLength currentCompact
        snapshot.heapCell snapshot.nextArena snapshot.nextAligned snapshot.arena scratchBelow (heapLower.trans grows) (dbBefore.trans grows)
        parentBound parentLower parentBefore payloadLower payloadUpper nibbleArena (by rw [nibbleNumber]; exact nibbleBound) currentInstalled value continued
    have frame : NormalFrame source post heap cursor limit:=
      (compactFrame.compose source ready inner heap cursor next cursor limit leafFrame grows (Nat.le_refl _)).of_erase source post inner heap cursor limit (by rw [endpoint]; rfl)
    have finalView : LeafView post next db pointer length heap (BitVec.ofNat 64 nibbles) valuePointer valueLength:=by
      apply leafView.of_fields post
      · rw [endpoint]; rfl
      · rw [endpoint]; rfl
    have finalArena : Rlp.Validation.Arena post cursor limit:=by
      apply leafArena.of_fields inner post cursor limit
      · rw [endpoint]; rfl
      · rw [endpoint]; rfl
    have finalCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)):=by
      rw [endpoint]
      exact finalHeapCell
    exact ⟨frame,BitVec.ofNat 64 nibbles,Or.inl ⟨next,valuePointer,valueLength,valueEq,finalView,grows,finalArena,finalHeap,finalCell,finalHeapArena,finalHeapAligned,nodeBefore⟩⟩
  · rw [if_neg isLeaf] at continued
    obtain ⟨valueEq,recordView,recordBefore,nextArena,nextCell,decreases⟩:=extension_view_normal ready inner db array pointer length listPointer heap (BitVec.ofNat 64 nibbles) leaf next cursor limit bytes items currentRows count currentArray currentPointer currentLength currentCompact
      snapshot.heapCell snapshot.arena below arrayFloor (beforeArray.trans grows) nibbleArena (by rw [nibbleNumber]; exact nibbleBound) heapLower
      (by rw [nibbleNumber]; have bound:=snapshot.nibbleBound; omega)
      parentBound parentLower parentBefore payloadLower payloadUpper currentInstalled value continued
    obtain ⟨nonempty,room,recordArena,scratch,recordUpper,drop,valueEq2,funding,postEq⟩:=extension_normal ready inner array pointer length heap (BitVec.ofNat 64 nibbles) leaf cursor limit
      currentArray currentPointer currentLength currentCompact snapshot.arena currentInstalled value continued
    have extensionFrame:=extension_frame_of_post ready inner next cursor limit (extensionWords array pointer length heap (BitVec.ofNat 64 nibbles)) snapshot.heapCell snapshot.nextArena snapshot.nextAligned snapshot.arena room scratch postEq
    have frame : NormalFrame source post heap cursor limit:=
      (compactFrame.compose source ready inner heap cursor next cursor limit extensionFrame grows (Nat.le_refl _)).of_erase source post inner heap cursor limit (by rw [endpoint]; rfl)
    have finalView : WitnessRecord.View post (WitnessRecord.pointer cursor) db (extensionDescription array pointer length listPointer bytes items heap (BitVec.ofNat 64 nibbles)):=by
      apply recordView.of_fields inner post _ db _
      · rw [endpoint]; rfl
      · rw [endpoint]; rfl
    have finalArena : Rlp.Validation.Arena post (WitnessRecord.pointer cursor) limit:=by
      apply nextArena.of_fields inner post _ limit
      · rw [endpoint]; rfl
      · rw [endpoint]; rfl
    have finalCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word next)):=by rw [endpoint]; exact nextCell
    exact ⟨frame,BitVec.ofNat 64 nibbles,Or.inr ⟨next,valueEq,finalView,recordBefore,finalCell,snapshot.nextArena,snapshot.nextAligned,grows,finalArena,decreases⟩⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.pair_normal
