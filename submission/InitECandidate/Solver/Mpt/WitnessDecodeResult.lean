import InitECandidate.Solver.Mpt.WitnessDecodeLeafView
import InitECandidate.Solver.Mpt.WitnessRecordFrame
import InitECandidate.Solver.Mpt.WitnessRecordArena

namespace InitECandidate.Solver.Mpt.WitnessRecord

/-- Actual new branch records start at index0/occupancy0. Extension
records have no branch counters. Later continuing records need not be fresh. -/
def Payload.Fresh : Payload→Prop
  | .extension ..=>True
  | .branch _ index occupied=>index.val=0 ∧ occupied.val=0

end InitECandidate.Solver.Mpt.WitnessRecord

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Physical normal outputs of the unchanged decoder. Fresh persistent
regions follow the incoming heap; record outputs carry actual scratch
progress and the real final heap. No already successful future call occurs
in this returned-state contract. -/
inductive NormalResult (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) : ValueHOL 64→Prop where
  | empty (scratch : Rlp.Validation.Arena post cursor limit) :
      NormalResult post db pointer length heap cursor limit (.rStruct [.val (.word 0#64),.val (.word 0#64)])
  | leaf (node nibbles nibbleLength valuePointer valueLength finalHeap : BitVec 64)
      (view : LeafView post node db pointer length nibbles nibbleLength valuePointer valueLength)
      (freshPath : heap.toNat≤nibbles.toNat) (freshNode : heap.toNat≤node.toNat)
      (scratch : Rlp.Validation.Arena post cursor limit)
      (heapCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)))
      (heapArena : AllocatedBytes.Arena finalHeap 0) (heapAligned : finalHeap.toNat%8=0) (nodeBefore : node.toNat+64≤finalHeap.toNat) :
      NormalResult post db pointer length heap cursor limit (.rStruct [.val (.word 0#64),.val (.word node)])
  | record (data : WitnessRecord.Description) (next : BitVec 64)
      (view : WitnessRecord.View post (WitnessRecord.pointer cursor) db data)
      (parentPointer : data.pointer=pointer) (parentLength : data.length=length)
      (before : data.BeforeHeap next.toNat)
      (freshRows : heap.toNat≤data.array.toNat) (freshPayload : heap.toNat≤data.payload.startAddress) (fresh : data.payload.Fresh)
      (heapCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word next)))
      (heapArena : AllocatedBytes.Arena next 0) (heapAligned : next.toNat%8=0)
      (scratch : Rlp.Validation.Arena post (WitnessRecord.pointer cursor) limit)
      (drop : ((WitnessRecord.pointer cursor).toNat-limit.toNat)/88+1≤(cursor.toNat-limit.toNat)/88) :
      NormalResult post db pointer length heap cursor limit (.rStruct [.val (.word 1#64),.val (.word (WitnessRecord.pointer cursor))])

theorem NormalResult.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) (value : ValueHOL 64)
    (result : NormalResult source db pointer length heap cursor limit value)
    (memory : target.memory=source.memory) (domain : target.memaddrs=source.memaddrs) (globals : target.globals=source.globals) :
    NormalResult target db pointer length heap cursor limit value := by
  cases result with
  | empty scratch=>exact .empty (scratch.of_fields source target cursor limit domain globals)
  | leaf node nibbles nibbleLength valuePointer valueLength finalHeap view freshPath freshNode scratch heapCell heapArena heapAligned nodeBefore=>
    exact .leaf node nibbles nibbleLength valuePointer valueLength finalHeap (view.of_fields target memory domain) freshPath freshNode
      (scratch.of_fields source target cursor limit domain globals) (by rw [globals]; exact heapCell) heapArena heapAligned nodeBefore
  | record data next view parentPointer parentLength before freshRows freshPayload fresh heapCell heapArena heapAligned scratch drop=>
    exact .record data next (view.of_fields source target _ db data memory domain) parentPointer parentLength before freshRows freshPayload fresh
      (by rw [globals]; exact heapCell) heapArena heapAligned (scratch.of_fields source target _ limit domain globals) drop

theorem NormalResult.weaken_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap smaller cursor limit : BitVec 64) (value : ValueHOL 64)
    (result : NormalResult source db pointer length heap cursor limit value) (lower : smaller.toNat≤heap.toNat) :
    NormalResult source db pointer length smaller cursor limit value := by
  cases result with
  | empty scratch=>exact .empty scratch
  | leaf node nibbles nibbleLength valuePointer valueLength finalHeap view freshPath freshNode scratch heapCell heapArena heapAligned nodeBefore=>
    exact .leaf node nibbles nibbleLength valuePointer valueLength finalHeap view (lower.trans freshPath) (lower.trans freshNode) scratch heapCell heapArena heapAligned nodeBefore
  | record data next view parentPointer parentLength before freshRows freshPayload fresh heapCell heapArena heapAligned scratch drop=>
    exact .record data next view parentPointer parentLength before (lower.trans freshRows) (lower.trans freshPayload) fresh heapCell heapArena heapAligned scratch drop

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.NormalResult.of_fields
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.NormalResult.weaken_heap
