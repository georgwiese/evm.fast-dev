import InitECandidate.Solver.Mpt.WitnessDecodePairNormal
import InitECandidate.Solver.Mpt.WitnessDecodeResult

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The real two-item result is either a physical leaf or a pending
extension. The already allocated row array is its allocation frontier;
the live frame separately uses the actual current heap at pair entry. -/
theorem current_pair_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db array pointer length listPointer heap cursor limit : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem)
    (rows : Rows source array listPointer bytes items) (count : items.length=2)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit)
    (beforeArray : array.toNat+16*items.length≤heap.toNat)
    (dbBefore : db.toNat≤heap.toNat)
    (parentBound : length.toNat≤1024) (parentLower : 2701131776≤pointer.toNat)
    (parentBefore : pointer.toNat+length.toNat≤db.toNat)
    (payloadLower : pointer.toNat≤listPointer.toNat) (payloadUpper : listPointer.toNat+bytes≤pointer.toNat+length.toNat)
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source pairBody=(some (.returned value),post)) :
    LiveFrame source post heap cursor limit ∧ NormalResult post db pointer length array cursor limit value := by
  obtain ⟨frame,nibbleLength,result⟩:=pair_normal source post db array pointer length listPointer heap cursor limit bytes items
    rows count arrayCell pointerCell lengthCell heapCell heapArena heapBound heapAligned live arena beforeArray dbBefore
    parentBound parentLower parentBefore payloadLower payloadUpper value normal
  have arrayBefore : array.toNat≤heap.toNat:=by omega
  refine ⟨frame,?_⟩
  rcases result with leaf|extension
  · obtain ⟨node,valuePointer,valueLength,valueEq,view,freshNode,scratch,finalHeap,finalCell,finalArena,finalAligned,nodeBefore,finalBound⟩:=leaf
    rw [valueEq]
    exact .leaf node heap nibbleLength valuePointer valueLength finalHeap view arrayBefore (arrayBefore.trans freshNode)
      scratch finalCell finalArena finalAligned nodeBefore
  · obtain ⟨next,valueEq,view,before,cell,allocation,aligned,grows,scratch,decreases⟩:=extension
    rw [valueEq]
    exact .record (extensionDescription array pointer length listPointer bytes items heap nibbleLength) next view rfl rfl before
      (Nat.le_refl _) arrayBefore True.intro True.intro cell allocation aligned scratch decreases

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_pair_frame
