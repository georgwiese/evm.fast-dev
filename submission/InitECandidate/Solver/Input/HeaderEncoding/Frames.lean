import InitECandidate.Solver.Input.HeaderEncoding.Call
import InitECandidate.Solver.Input.VarList.RecordCells

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack PanSemStateFiniteExact

/-- Preserving old aligned cells preserves every copied input byte. The
mathematical input length is still reduced only at the encoded interface. -/
theorem OldMemory.heap_input (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer buffer : BitVec 64) (frame : OldMemory target.memory source.memory buffer)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (before : pointer.toNat+input.length%2^64≤buffer.toNat) (heap : Blob.HeapInput source input pointer) :
    Blob.HeapInput target input pointer := by
  classical
  intro offset inside
  have limit:=buffer.isLt
  have number:=WitnessRadix.byteAddress_toNat pointer offset (by omega)
  change (pointer+BitVec.ofNat 64 offset).toNat=pointer.toNat+offset at number
  have aligned:=WitnessRadix.AllocatedBytes.aligned_number (pointer+BitVec.ofNat 64 offset)
  have cell : target.memory (panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 offset))=
      source.memory (panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 offset)) :=
    frame _ (by rw [aligned,number]; omega)
  have read:=heap offset inside
  simpa only [panMemLoadByteHOL,cell,domain,endian] using read

/-- The same old-cell frame preserves the actual decoder record array.
Empty slices require no allocation or record-cell premise. -/
theorem OldMemory.records (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array buffer : BitVec 64) (start length : Nat) (frame : OldMemory target.memory source.memory buffer)
    (before : length≠0→array.toNat+16*VarList.decodedCount input start length≤buffer.toNat)
    (records : VarList.Records source input pointer array start length) : VarList.Records target input pointer array start length := by
  rcases records with empty|nonempty
  · exact Or.inl empty
  · obtain ⟨plan,p,a,s,n,c,complete,valid⟩:=nonempty
    have positive:=plan.positive
    have header:=plan.header
    have nonzero : length≠0 := by rw [n] at header; omega
    have count : plan.count=VarList.decodedCount input start length := by simp only [VarList.decodedCount,if_neg nonzero,←c]
    have arrayBefore:=before nonzero
    refine Or.inr ⟨plan,p,a,s,n,c,?_,valid⟩
    intro index inside
    have rowNumber:=plan.row_nat index inside
    have lengthNumber:=plan.length_nat index inside
    have first : target.memory (VarList.row plan.array index)=source.memory (VarList.row plan.array index) := by
      apply frame
      rw [rowNumber,a,count] at *
      omega
    have second : target.memory (VarList.lengthCell plan.array index)=source.memory (VarList.lengthCell plan.array index) := by
      apply frame
      rw [lengthNumber,a,count] at *
      omega
    rw [first,second]
    exact complete index inside

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.OldMemory.heap_input
#print axioms InitECandidate.Solver.Input.HeaderEncoding.OldMemory.records
