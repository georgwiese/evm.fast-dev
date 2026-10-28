import InitECandidate.Solver.Headers.ValidateRows
import InitECandidate.Solver.Input.CurrentStartup.WitnessArrayImage
import InitECandidate.Solver.Input.VarList.ArrayGeometry

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack PanSemStateFiniteExact Input WitnessRadix

/-- The actual bounded witness-array image supplies every validator row.
An empty list requires no readable zero pointer or invented sentinel record. -/
theorem rows_from_image {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si array : BitVec 64} {start length boundary : Nat}
    (data : CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary 72 1024 256)
    (domain : source.memaddrs=InitE.ordinaryDomain) :
    Rows source (VarList.decodedArray array length) (VarList.recordPointer input pointer start)
      (VarList.recordLength input start length (VarList.decodedCount input start length))
      (VarList.decodedCount input start length) 2701134640 boundary := by
  by_cases empty : length=0
  · constructor <;> simp [VarList.decodedCount,empty]
  · have geometry:=data.records.array_geometry source input pointer array start length empty
    let count:=VarList.decodedCount input start length
    have arrayArena : AllocatedBytes.Arena array (16*count) := ⟨geometry.2.1,geometry.2.2.2.1⟩
    have cells:=data.records.pointer_cells source input pointer array start length
    have lengths:=data.records.cells source input pointer array start length domain
    have inputs:=data.records.slice_geometry source input pointer array start length
    have rowNumber (index : Nat) (inside : index<count) : (byteAddress array (16*index)).toNat=array.toNat+16*index :=
      MemoryBytes.offset_toNat array (16*index) (by have h:=arrayArena.upper; omega)
    simp only [VarList.decodedArray,if_neg empty] at cells lengths ⊢
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro index inside
      exact ⟨cells index inside,(lengths.2.2 index inside).2⟩
    · intro index inside
      exact arrayArena.subrange array (16*count) (16*index) 16 (by omega)
    · intro index inside
      rw [rowNumber index inside]
      have aligned:=geometry.2.2.1
      omega
    · intro index inside
      rw [rowNumber index inside]
      have after:=geometry.2.2.2.2
      have lower:=data.inputLower
      omega
    · intro index inside
      rw [rowNumber index inside]
      have before:=data.before
      change array.toNat+16*count≤boundary at before
      omega
    · intro index inside
      exact (inputs index inside).2.2.1
    · intro index inside
      rw [(inputs index inside).1]
      have lower:=data.inputLower
      omega
    · intro index inside
      have before:=(inputs index inside).2.2.2
      have arrayBefore:=data.before
      change array.toNat+16*count≤boundary at arrayBefore
      omega
    · intro index inside
      have size:=data.lengths index inside
      omega

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.rows_from_image
