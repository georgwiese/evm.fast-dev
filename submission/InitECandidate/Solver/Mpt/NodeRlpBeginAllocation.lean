import InitECandidate.Solver.Mpt.NodeRlpBeginFlagsNormal
import InitECandidate.Solver.Input.AllocationLocalNormal

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def allocationAmount (length : BitVec 64) : BitVec 64:=(length >>> (1 : Nat))+2#64
def allocationCall : ProgHOL 64:=.call (some (some (.local,ofString "cbuf"),none)) (ofString "alloc") allocationArguments

theorem allocation_amount (length : BitVec 64) : (allocationAmount length).toNat=length.toNat/2+2 := by
  have shifted : (length >>> (1 : Nat)).toNat=length.toNat/2:=by
    rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  rw [allocationAmount,BitVec.toNat_add_of_lt (by rw [shifted]; change length.toNat/2+2<2^64; have :=length.isLt; omega),shifted]
  rfl

theorem allocation_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (lengthCell : source.locals.lookup (ofString "nlen")=some (.val (.word length))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) allocationArguments=some (PersistentAlloc.values (allocationAmount length)) := by
  simp [allocationArguments,PersistentAlloc.values,allocationAmount,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,lengthCell,
    wordShiftHOL,valueIsWord,valueWord,wordOpHOL,wordOp]

/-- Present path operands and persistent heap frontier, before the actual
assigned alloc. The value fields are older live words; no room or future
successful allocation is asserted here. -/
structure PathInput (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag pathLength : BitVec 64)
    (limit : Nat) (property : BitVec 64→BitVec 64→Prop) where
  pointer : BitVec 64
  heap : BitVec 64
  oldBuffer : BitVec 64
  nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node))
  tagCell : source.locals.lookup (ofString "k")=some (.val (.word tag))
  pathCell : source.locals.lookup (ofString "nlen")=some (.val (.word pathLength))
  bufferCell : source.locals.lookup (ofString "cbuf")=some (.val (.word oldBuffer))
  pointerMapped : source.memaddrs (node+32#64)
  pointerStored : source.memory (node+32#64)=.word pointer
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapLower : 2701131776≤heap.toNat
  heapUpper : heap.toNat≤2952790016
  heapAligned : heap.toNat%8=0
  domain : source.memaddrs=InitE.ordinaryDomain
  value : tag=1#64→TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 limit property
  valueBelow : tag=1#64→(node+48#64).toNat<heap.toNat ∧ (node+56#64).toNat<heap.toNat

theorem fresh_output_away (heap query : BitVec 64) (size offset : Nat)
    (aligned : heap.toNat%8=0) (older : query.toNat<heap.toNat)
    (room : heap.toNat+size≤2952790016) (inside : offset<size) :
    query≠panByteAlignHOL (width:=64) (byteAddress heap offset) := by
  intro equal
  have number:=byteAddress_toNat heap offset (by omega)
  have same:=congrArg BitVec.toNat equal
  rw [AllocatedBytes.aligned_number,number] at same
  omega

/-- The actual allocation derives room and its exact state, then produces
the compact writer's current operands. Freshness of its real buffer derives
value-field separation, rather than assuming later writer preservation. -/
theorem after_real_allocation (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag pathLength : BitVec 64)
    (limit : Nat) (property : BitVec 64→BitVec 64→Prop) (data : PathInput source node tag pathLength limit property)
    (installed : Input.OriginalCode.Installed source.code) (normal : evaluateHOLFiniteState source allocationCall=(none,target)) :
    data.heap.toNat+pathLength.toNat/2+2≤2952790016 ∧
      target=bind (PersistentAlloc.post {source with clock:=source.clock-1} data.heap (allocationAmount pathLength)) "cbuf" data.heap ∧
      Nonempty (CompactData (bind target "isl" 0#64) node tag data.heap pathLength limit property) := by
  obtain ⟨room,_funded,endpoint⟩:=PersistentAlloc.local_call_normal source target "cbuf" data.oldBuffer data.heap (allocationAmount pathLength) data.bufferCell allocationArguments
    (allocation_arguments source pathLength data.pathCell) (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed)
    data.heapCell data.heapUpper normal
  rw [allocation_amount] at room
  have bufferMapped : source.memaddrs (panByteAlignHOL (width:=64) data.heap):=by
    rw [data.domain]
    exact AllocatedBytes.ordinary_byte_mapped data.heap data.heapLower (by omega)
  refine ⟨by omega,endpoint,?_⟩
  rw [endpoint]
  let allocated:=bind (PersistentAlloc.post {source with clock:=source.clock-1} data.heap (allocationAmount pathLength)) "cbuf" data.heap
  refine ⟨{
    pointer:=data.pointer
    leaf:=0#64
    nodeCell:=(bind_lookup_other allocated "isl" "node" 0#64 (by decide)).trans
      ((bind_lookup_other _ "cbuf" "node" data.heap (by decide)).trans data.nodeCell)
    tagCell:=(bind_lookup_other allocated "isl" "k" 0#64 (by decide)).trans
      ((bind_lookup_other _ "cbuf" "k" data.heap (by decide)).trans data.tagCell)
    bufferCell:=(bind_lookup_other allocated "isl" "cbuf" 0#64 (by decide)).trans (bind_lookup_same _ _ _)
    pathCell:=(bind_lookup_other allocated "isl" "nlen" 0#64 (by decide)).trans
      ((bind_lookup_other _ "cbuf" "nlen" data.heap (by decide)).trans data.pathCell)
    leafCell:=bind_lookup_same _ _ _
    pointerMapped:=data.pointerMapped
    pointerStored:=data.pointerStored
    bufferMapped:=bufferMapped
    value:=data.value
    valueAway:=by
      intro leaf offset inside
      exact ⟨fresh_output_away data.heap (node+48#64) (pathLength.toNat/2+2) offset data.heapAligned (data.valueBelow leaf).1 room (by omega),
        fresh_output_away data.heap (node+56#64) (pathLength.toNat/2+2) offset data.heapAligned (data.valueBelow leaf).2 room (by omega)⟩ }⟩

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.allocation_amount
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.allocation_arguments
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.fresh_output_away
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.after_real_allocation
