import InitECandidate.Solver.Headers.ValidateRows
import InitECandidate.Solver.Input.VarList.ConstructorData

namespace InitECandidate.Solver.Headers.Validate
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The original SSZ decoder's actual records supply the validator row
contract. Empty lists retain their original zero-array convention and
introduce no fictitious readable record. -/
theorem Rows.of_records (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length lower upper : Nat)
    (records : Input.VarList.Records source input pointer array start length)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (inputAfter : lower≤pointer.toNat) (arrayAfter : lower≤array.toNat)
    (arrayBefore : array.toNat+16*Input.VarList.decodedCount input start length≤upper) (lengthBound : length≤134217712) :
    Rows source (Input.VarList.decodedArray array length) (Input.VarList.recordPointer input pointer start)
      (Input.VarList.recordLength input start length (Input.VarList.decodedCount input start length))
      (Input.VarList.decodedCount input start length) lower upper := by
  by_cases empty : length=0
  · constructor <;> simp [Input.VarList.decodedCount,empty]
  · have geometry:=records.array_geometry source input pointer array start length empty
    let count:=Input.VarList.decodedCount input start length
    have arrayArena : AllocatedBytes.Arena array (16*count) := ⟨geometry.2.1,geometry.2.2.2.1⟩
    have cells:=records.pointer_cells source input pointer array start length
    have lengths:=records.cells source input pointer array start length domain
    have inputs:=records.slice_geometry source input pointer array start length
    have rowNumber (index : Nat) (inside : index<count) : (byteAddress array (16*index)).toNat=array.toNat+16*index :=
      MemoryBytes.offset_toNat array (16*index) (by have h:=arrayArena.upper; omega)
    simp only [Input.VarList.decodedArray,if_neg empty] at cells lengths ⊢
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
      omega
    · intro index inside
      rw [rowNumber index inside]
      change array.toNat+16*count≤upper at arrayBefore
      omega
    · intro index inside
      exact (inputs index inside).2.2.1
    · intro index inside
      rw [(inputs index inside).1]
      omega
    · intro index inside
      have before:=(inputs index inside).2.2.2
      change array.toNat+16*count≤upper at arrayBefore
      omega
    · intro index inside
      have size:=(inputs index inside).2.1
      omega

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.Rows.of_records
