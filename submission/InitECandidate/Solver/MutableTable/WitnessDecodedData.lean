import InitECandidate.Solver.Input.VarList.ConstructorData
import InitECandidate.Solver.MutableTable.WitnessBuildRecords
import InitECandidate.Solver.WitnessRadix.BufferRegionBelow

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes

/-- The exact slices stored by decode_bytes_list, indexed by the constructor's
actual word-valued ordinal. -/
def decodedSlice (input : Guest.InputBlob) (pointer : BitVec 64) (start length : Nat) (index : BitVec 64) : Graph.Slice:=
  (Input.VarList.recordPointer input pointer start index.toNat,
   Input.VarList.recordLength input start length (Input.VarList.decodedCount input start length) index.toNat)

/-- Nonempty decoder results discharge the constructor's actual record reads,
record arena and public hash-buffer premises. The heap boundary and fixed hash
buffer allocations remain explicit whole-program reachability obligations. -/
theorem decoded_constructor_data (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length boundary : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (decoded : Input.VarList.Records source input pointer array start length) (nonemptyLength : length≠0)
    (arrayBefore : array.toNat+16*Input.VarList.decodedCount input start length≤boundary)
    (stp pad out : BitVec 64) (stateArena : Arena stp 200) (stateAligned : stp.toNat%8=0)
    (paddingArena : Arena pad 136) (paddingAligned : pad.toNat%8=0) (outputArena : Arena out 32)
    (buffersBefore : stp.toNat+200≤array.toNat ∧ pad.toNat+136≤array.toNat ∧ out.toNat+32≤array.toNat) :
    let count:=Input.VarList.decodedCount input start length
    let sliceFor:=decodedSlice input pointer start length
    0<count ∧ 2701131776≤array.toNat ∧ array.toNat%8=0 ∧
    (∀ index<count,source.memory (byteAddress (BitVec.ofNat 64 array.toNat) (16*index))=.word (sliceFor (BitVec.ofNat 64 index)).1) ∧
    (∀ index<count,source.memory (byteAddress (BitVec.ofNat 64 array.toNat) (16*index+8))=.word (sliceFor (BitVec.ofNat 64 index)).2) ∧
    (∀ index<count,Keccak256.Buffers stp (sliceFor (BitVec.ofNat 64 index)).1 pad out (sliceFor (BitVec.ofNat 64 index)).2.toNat) ∧
    (∀ index<count,Keccak256.BufferRegion (fun query=>query.toNat<boundary) stp
      (sliceFor (BitVec.ofNat 64 index)).1 pad out (sliceFor (BitVec.ofNat 64 index)).2.toNat) ∧
    (∀ index<count,(byteAddress (BitVec.ofNat 64 array.toNat) (16*index)).toNat<boundary ∧
      (byteAddress (BitVec.ofNat 64 array.toNat) (16*index+8)).toNat<boundary) := by
  classical
  let count:=Input.VarList.decodedCount input start length
  let sliceFor:=decodedSlice input pointer start length
  obtain ⟨positive,lower,aligned,room,after⟩:=Input.VarList.Records.array_geometry source input pointer array start length decoded nonemptyLength
  obtain ⟨_,small,lengthCells⟩:=Input.VarList.Records.cells source input pointer array start length domain decoded
  have pointerCells:=Input.VarList.Records.pointer_cells source input pointer array start length decoded
  have hashBuffers:=Input.VarList.Records.hash_buffers source input pointer array start length decoded stp pad out
    stateArena stateAligned paddingArena paddingAligned outputArena
  have sliceAt (index : Nat) (inside : index<count) :
      decodedSlice input pointer start length (BitVec.ofNat 64 index)=
        (Input.VarList.recordPointer input pointer start index,Input.VarList.recordLength input start length count index) := by
    have fits : index<2^64 := by change count<2^31 at small;omega
    simp only [decodedSlice,BitVec.toNat_ofNat,Nat.mod_eq_of_lt fits]
    rfl
  have arrayValue : Input.VarList.decodedArray array length=array := by simp only [Input.VarList.decodedArray,if_neg nonemptyLength]
  change 0<count ∧ _
  refine ⟨positive,lower,aligned,?_,?_,?_,?_,?_⟩
  · intro index inside
    rw [sliceAt index inside,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    change source.memory (Input.VarList.row array index)=_
    rw [←arrayValue]
    exact pointerCells index inside
  · intro index inside
    rw [sliceAt index inside,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    have address : byteAddress array (16*index+8)=Input.VarList.lengthCell array index := by
      simp [byteAddress,Input.VarList.lengthCell,Input.VarList.row,BitVec.ofNat_add,BitVec.add_assoc]
    rw [address,←arrayValue]
    exact (lengthCells index inside).2
  · intro index inside
    rw [sliceAt index inside]
    exact hashBuffers index inside
  · intro index inside
    rw [sliceAt index inside]
    have geometry:=Input.VarList.Records.slice_geometry source input pointer array start length decoded index inside
    apply Keccak256.buffer_region_below stp _ pad out _ boundary (hashBuffers index inside)
    refine ⟨?_,?_,?_,?_⟩
    · have:=buffersBefore.1;omega
    · have:=geometry.2.2.2;omega
    · have:=buffersBefore.2.1;omega
    · have:=buffersBefore.2.2;omega
  · intro index inside
    rw [BitVec.ofNat_toNat,BitVec.setWidth_eq]
    have first:=byteAddress_toNat array (16*index) (by change array.toNat+16*count≤33806089496 at room;omega)
    have second:=byteAddress_toNat array (16*index+8) (by change array.toNat+16*count≤33806089496 at room;omega)
    rw [first,second]
    omega

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.decoded_constructor_data
