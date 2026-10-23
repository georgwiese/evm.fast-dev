import InitECandidate.Solver.Mpt.WitnessDecodeResult
import InitECandidate.Solver.Mpt.TriePathBytes

namespace InitECandidate.Solver.Mpt.WitnessRecord
open Flapjack PanSemStateFiniteExact

/-- Pending extension records retain their actual full nibble buffer.
Branch records have no path buffer. -/
def Payload.PathBytes (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Payload→Prop
  | .extension pointer length=>TrieWalk.NibbleSpan source.memory source.memaddrs source.be pointer length.toNat ∧ pointer.toNat%8=0
  | .branch ..=>True

theorem Payload.PathBytes.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (payload : Payload) (bytes : payload.PathBytes source)
    (memory : target.memory=source.memory) (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be) :
    payload.PathBytes target := by
  cases payload with
  | extension pointer length=>
    exact ⟨bytes.1.of_agreement source.memory target.memory source.memaddrs target.memaddrs source.be target.be pointer length.toNat
      domain endian (by intro offset inside; rw [memory]),bytes.2⟩
  | branch node index occupied=>trivial

end InitECandidate.Solver.Mpt.WitnessRecord

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Physical normal outputs of the unchanged decoder. Fresh persistent
regions follow the incoming heap; record outputs carry actual scratch
progress and the real final heap. No already successful future call occurs
in this returned-state contract. -/
inductive NibbleResult (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) : ValueHOL 64→Prop where
  | empty (scratch : Rlp.Validation.Arena post cursor limit) :
      NibbleResult post db pointer length heap cursor limit (.rStruct [.val (.word 0#64),.val (.word 0#64)])
  | leaf (node nibbles nibbleLength valuePointer valueLength finalHeap : BitVec 64)
      (view : LeafView post node db pointer length nibbles nibbleLength valuePointer valueLength)
      (freshPath : heap.toNat≤nibbles.toNat) (freshNode : heap.toNat≤node.toNat)
      (scratch : Rlp.Validation.Arena post cursor limit)
      (heapCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)))
      (heapArena : AllocatedBytes.Arena finalHeap 0) (heapAligned : finalHeap.toNat%8=0) (nodeBefore : node.toNat+64≤finalHeap.toNat)
      (pathBytes : TrieWalk.NibbleSpan post.memory post.memaddrs post.be nibbles nibbleLength.toNat)
      (pathAligned : nibbles.toNat%8=0) (pathBefore : nibbles.toNat+nibbleLength.toNat≤node.toNat) :
      NibbleResult post db pointer length heap cursor limit (.rStruct [.val (.word 0#64),.val (.word node)])
  | record (data : WitnessRecord.Description) (next : BitVec 64)
      (view : WitnessRecord.View post (WitnessRecord.pointer cursor) db data)
      (parentPointer : data.pointer=pointer) (parentLength : data.length=length)
      (before : data.BeforeHeap next.toNat)
      (freshRows : heap.toNat≤data.array.toNat) (freshPayload : heap.toNat≤data.payload.startAddress) (fresh : data.payload.Fresh) (initial : data.payload.InitialValue post)
      (heapCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word next)))
      (heapArena : AllocatedBytes.Arena next 0) (heapAligned : next.toNat%8=0)
      (scratch : Rlp.Validation.Arena post (WitnessRecord.pointer cursor) limit)
      (drop : ((WitnessRecord.pointer cursor).toNat-limit.toNat)/88+1≤(cursor.toNat-limit.toNat)/88)
      (pathBytes : data.payload.PathBytes post) :
      NibbleResult post db pointer length heap cursor limit (.rStruct [.val (.word 1#64),.val (.word (WitnessRecord.pointer cursor))])

theorem NibbleResult.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) (value : ValueHOL 64)
    (result : NibbleResult source db pointer length heap cursor limit value)
    (memory : target.memory=source.memory) (domain : target.memaddrs=source.memaddrs) (globals : target.globals=source.globals) (endian : target.be=source.be) :
    NibbleResult target db pointer length heap cursor limit value := by
  cases result with
  | empty scratch=>exact .empty (scratch.of_fields source target cursor limit domain globals)
  | leaf node nibbles nibbleLength valuePointer valueLength finalHeap view freshPath freshNode scratch heapCell heapArena heapAligned nodeBefore pathBytes pathAligned pathBefore=>
    exact .leaf node nibbles nibbleLength valuePointer valueLength finalHeap (view.of_fields target memory domain) freshPath freshNode
      (scratch.of_fields source target cursor limit domain globals) (by rw [globals]; exact heapCell) heapArena heapAligned nodeBefore
      (pathBytes.of_agreement source.memory target.memory source.memaddrs target.memaddrs source.be target.be nibbles nibbleLength.toNat
        domain endian (by intro offset inside; rw [memory])) pathAligned pathBefore
  | record data next view parentPointer parentLength before freshRows freshPayload fresh initial heapCell heapArena heapAligned scratch drop pathBytes=>
    exact .record data next (view.of_fields source target _ db data memory domain) parentPointer parentLength before freshRows freshPayload fresh (initial.of_fields source target data.payload memory)
      (by rw [globals]; exact heapCell) heapArena heapAligned (scratch.of_fields source target _ limit domain globals) drop (pathBytes.of_fields source target data.payload memory domain endian)

theorem NibbleResult.weaken_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap smaller cursor limit : BitVec 64) (value : ValueHOL 64)
    (result : NibbleResult source db pointer length heap cursor limit value) (lower : smaller.toNat≤heap.toNat) :
    NibbleResult source db pointer length smaller cursor limit value := by
  cases result with
  | empty scratch=>exact .empty scratch
  | leaf node nibbles nibbleLength valuePointer valueLength finalHeap view freshPath freshNode scratch heapCell heapArena heapAligned nodeBefore pathBytes pathAligned pathBefore=>
    exact .leaf node nibbles nibbleLength valuePointer valueLength finalHeap view (lower.trans freshPath) (lower.trans freshNode) scratch heapCell heapArena heapAligned nodeBefore pathBytes pathAligned pathBefore
  | record data next view parentPointer parentLength before freshRows freshPayload fresh initial heapCell heapArena heapAligned scratch drop pathBytes=>
    exact .record data next view parentPointer parentLength before (lower.trans freshRows) (lower.trans freshPayload) fresh initial heapCell heapArena heapAligned scratch drop pathBytes

/-- Forget only the additional proved path bytes when using an older API. -/
theorem NibbleResult.normal_result (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) (value : ValueHOL 64)
    (result : NibbleResult source db pointer length heap cursor limit value) :
    NormalResult source db pointer length heap cursor limit value := by
  cases result with
  | empty scratch=>exact .empty scratch
  | leaf node nibbles nibbleLength valuePointer valueLength finalHeap view freshPath freshNode scratch heapCell heapArena heapAligned nodeBefore pathBytes pathAligned pathBefore=>
    exact .leaf node nibbles nibbleLength valuePointer valueLength finalHeap view freshPath freshNode scratch heapCell heapArena heapAligned nodeBefore
  | record data next view parentPointer parentLength before freshRows freshPayload fresh initial heapCell heapArena heapAligned scratch drop pathBytes=>
    exact .record data next view parentPointer parentLength before freshRows freshPayload fresh initial heapCell heapArena heapAligned scratch drop

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.NibbleResult.of_fields
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.NibbleResult.weaken_heap

#print axioms InitECandidate.Solver.Mpt.WitnessRecord.Payload.PathBytes.of_fields
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.NibbleResult.normal_result
