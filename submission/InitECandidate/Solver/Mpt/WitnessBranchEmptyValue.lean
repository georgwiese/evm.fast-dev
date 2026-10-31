import InitECandidate.Solver.Mpt.WitnessCoreBranchValueStores
import InitECandidate.Solver.Mpt.WitnessDecodeBranchNormal
import InitECandidate.Solver.Mpt.WitnessRecordMemory

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The final two actual word-zero stores initialize the branch value
words, independently of all prior memory contents. -/
theorem branch_allocated_empty (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) :
    WitnessCore.EmptyValue (branchAllocated source heap) heap := by
  have away : heap+160#64≠heap+168#64 := by
    intro equal
    exact (by decide : (160#64 : BitVec 64)≠168#64) ((BitVec.add_right_inj heap).mp equal)
  have away160 : heap+160#64≠heap := by
    intro equal
    have zero : (160#64 : BitVec 64)=0#64 := (BitVec.add_right_inj heap).mp (by simpa only [BitVec.add_zero] using equal)
    cases zero
  have away168 : heap+168#64≠heap := by
    intro equal
    have zero : (168#64 : BitVec 64)=0#64 := (BitVec.add_right_inj heap).mp (by simpa only [BitVec.add_zero] using equal)
    cases zero
  constructor
  · change StoreWord.put (StoreWord.put (StoreWord.put (Zero.memory32 source.memory heap 0 5) (heap+160#64) 0#64) (heap+168#64) 0#64) heap 3#64 (heap+160#64)=.word 0#64
    simp [StoreWord.put,away160,away]
  · change StoreWord.put (StoreWord.put (StoreWord.put (Zero.memory32 source.memory heap 0 5) (heap+160#64) 0#64) (heap+168#64) 0#64) heap 3#64 (heap+168#64)=.word 0#64
    simp [StoreWord.put,away168]

/-- The real branch decoder's scratch-record stores retain those zero
value words in its genuine returned physical state. -/
theorem branch_empty_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer length count heap cursor limit : BitVec 64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (sliceCell : source.locals.lookup (ofString "sl")=some (Rlp.Slices.result array count))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit)
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source branchBody=(some (.returned value),target)) : WitnessCore.EmptyValue target heap := by
  obtain ⟨countEq,nodeRoom,nodeArena,room,recordArena,nextArena,decreases,valueEq,funded,post⟩ := branch_normal source target array pointer length count heap cursor limit
    arrayCell pointerCell lengthCell sliceCell heapCell heapArena heapAligned arena live.code value normal
  obtain ⟨limitLower,cursorUpper⟩:=live.bounds arena
  have memory:=congrArg PanSemStateFiniteExact.memory post
  change target.memory=WordWrites.write (branchAllocated source heap).memory
    (LocalFields.writes (WitnessRecord.pointer cursor) (branchFields (branchWords array pointer length heap))) at memory
  apply (branch_allocated_empty source heap).frame (branchAllocated source heap) target heap
  all_goals
    rw [memory]
    apply WitnessRecord.writes_outside source cursor limit arena room _
      (by intro field member; have geometry:=branch_geometry (branchWords array pointer length heap) field member; omega)
    apply Or.inl
    have upper:=nodeArena.upper
    have number160 : (heap+160#64).toNat=heap.toNat+160 := byteAddress_toNat heap 160 (by omega)
    have number168 : (heap+168#64).toNat=heap.toNat+168 := byteAddress_toNat heap 168 (by omega)
    omega

end InitECandidate.Solver.Mpt.WitnessDecode

namespace InitECandidate.Solver.Mpt.WitnessRecord
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- A freshly returned branch has its genuine original empty value;
extension records have no branch value words. -/
def Payload.InitialValue (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Payload → Prop
  | .extension ..=>True
  | .branch node _ _=>WitnessCore.EmptyValue source node

theorem Payload.InitialValue.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (payload : Payload) (initial : payload.InitialValue source) (memory : target.memory=source.memory) : payload.InitialValue target := by
  cases payload with
  | extension nibbles length=>trivial
  | branch node index occupied=>exact ⟨by rw [memory]; exact initial.1,by rw [memory]; exact initial.2⟩

/-- The core's actual PREV store is above every branch allocation and
therefore retains the freshly derived initial value fields. -/
theorem Payload.InitialValue.store_record (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db previous : BitVec 64) (data : Description) (view : View source record db data)
    (initial : data.payload.InitialValue source) :
    data.payload.InitialValue {source with memory:=StoreWord.put source.memory record previous} := by
  cases payload : data.payload with
  | extension nibbles length=>simp only [InitialValue,payload]
  | branch node index occupied=>
    simp only [InitialValue,payload] at initial ⊢
    have owned:=view.owned
    simp only [payload,Payload.Owned] at owned
    have payloadBefore:=view.payload_before_record source record db data
    simp only [payload,Payload.endAddress] at payloadBefore
    have away (offset : Nat) (inside : offset<176) : node+BitVec.ofNat 64 offset≠record := by
      have number : (node+BitVec.ofNat 64 offset).toNat=node.toNat+offset := byteAddress_toNat node offset (by have upper:=owned.1.upper; omega)
      intro equal
      have numeric:=congrArg BitVec.toNat equal
      rw [number] at numeric
      omega
    exact initial.frame source _ node (if_neg (away 160 (by decide))) (if_neg (away 168 (by decide)))

end InitECandidate.Solver.Mpt.WitnessRecord

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_allocated_empty
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_empty_normal
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.Payload.InitialValue.store_record
