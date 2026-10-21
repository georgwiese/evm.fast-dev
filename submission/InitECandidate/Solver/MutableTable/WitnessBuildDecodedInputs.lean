import InitECandidate.Solver.Input.VarList.ConstructorData
import InitECandidate.Solver.MutableTable.WitnessBuildInputsAfter

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Genuine SSZ decoder records supply every caller-side row and hash-buffer
premise of the original witness constructor. Current startup globals and
heap room remain explicit physical reachability facts. -/
theorem Inputs.of_decoded (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array heap : BitVec 64) (start length maximum : Nat) (stp pad scratch : BitVec 64)
    (records : Input.VarList.Records source input pointer array start length)
    (installed : Input.OriginalCode.Installed source.code) (environment : Keccak256.Environment source stp pad)
    (scratchGlobal : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word scratch)))
    (little : source.be=false) (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (room : heap.toNat+72+57*(4*Input.VarList.decodedCount input start length+4)+7≤33806089496)
    (arrayBefore : array.toNat+16*Input.VarList.decodedCount input start length≤heap.toNat)
    (stateArena : AllocatedBytes.Arena stp 200) (stateAligned : stp.toNat%8=0)
    (padArena : AllocatedBytes.Arena pad 136) (padAligned : pad.toNat%8=0) (scratchArena : AllocatedBytes.Arena scratch 32)
    (buffersBefore : stp.toNat+200≤array.toNat ∧ pad.toNat+136≤array.toNat ∧ scratch.toNat+32≤array.toNat)
    (scratchAligned : scratch.toNat%8=0)
    (sizes : ∀ index<Input.VarList.decodedCount input start length,
      (Input.VarList.recordLength input start length (Input.VarList.decodedCount input start length) index).toNat≤maximum) :
    Inputs source (Input.VarList.decodedArray array length) heap (Input.VarList.decodedCount input start length) maximum
      (decodedSlices input pointer start length) stp pad scratch := by
  have pointerCells:=Input.VarList.Records.pointer_cells source input pointer array start length records
  have lengthCells:=Input.VarList.Records.cells source input pointer array start length environment.domain records
  have buffers:=Input.VarList.Records.hash_buffers source input pointer array start length records stp pad scratch stateArena stateAligned padArena padAligned scratchArena
  have arrayOf (positive : Input.VarList.decodedCount input start length≠0) : Input.VarList.decodedArray array length=array := by
    have nonempty : length≠0 := by intro empty; simp [Input.VarList.decodedCount,empty] at positive
    simp [Input.VarList.decodedArray,nonempty]
  refine ⟨installed,environment,scratchGlobal,little,heapGlobal,heapLower,heapAligned,room,?_,?_,?_,buffers,?_,scratchAligned,sizes⟩
  · intro positive
    have nonempty : length≠0 := by intro empty; simp [Input.VarList.decodedCount,empty] at positive
    obtain ⟨countPositive,lower,aligned,upper,afterInput⟩ := Input.VarList.Records.array_geometry source input pointer array start length records nonempty
    rw [arrayOf positive]
    exact ⟨lower,arrayBefore,aligned⟩
  · intro index inside
    simpa only [Input.VarList.row,byteAddress,decodedSlices] using pointerCells index inside
  · intro index inside
    simpa only [Input.VarList.lengthCell,Input.VarList.row,byteAddress,decodedSlices,BitVec.ofNat_add,BitVec.add_assoc] using (lengthCells.2.2 index inside).2
  · intro positive
    rw [arrayOf positive]
    exact buffersBefore

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Inputs.of_decoded
