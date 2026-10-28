import InitECandidate.Solver.Headers.ValidateRows
import InitECandidate.Solver.Input.CurrentStartup.WitnessArrayImage
import InitECandidate.Solver.Input.VarList.ArrayGeometry

namespace InitECandidate.Solver.Input.CurrentStartup.WitnessArrays
open Headers.Validate
open Flapjack PanSemStateFiniteExact Input WitnessRadix

/-- Any actual bounded witness-array image supplies the physical hash rows.
An empty list requires no readable zero pointer or invented sentinel record. -/
theorem Image.rows {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si array : BitVec 64} {start length boundary offset itemLimit countLimit : Nat}
    (data : Image input source pointer si array start length boundary offset itemLimit countLimit)
    (domain : source.memaddrs=InitE.ordinaryDomain) (sizeBound : 16*itemLimit<2^64) :
    Rows source (VarList.decodedArray array length) (VarList.recordPointer input pointer start)
      (VarList.recordLength input start length (VarList.decodedCount input start length))
      (VarList.decodedCount input start length) 2701134824 boundary := by
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

end InitECandidate.Solver.Input.CurrentStartup.WitnessArrays

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessArrays.Image.rows
