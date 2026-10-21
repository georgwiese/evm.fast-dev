import InitECandidate.Solver.Input.Witness.Inputs
import InitECandidate.Solver.Input.VarList.ConstructorData
import InitECandidate.Solver.Input.VarList.RecordByteBudget

namespace InitECandidate.Solver.Input.Witness
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Every actual decoded header row lies before the original decoder's
allocation frontier. Its byte length is bounded by the common input budget,
without assuming a successful later header parse or a nonempty byte slice. -/
theorem Inputs.header_slice_geometry (current : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array si codeArray headerArray frontier : BitVec 64) (start first middle last total : Nat)
    (inputs : Inputs current input pointer array si codeArray headerArray frontier start first middle last total)
    (inputBudget : total≤input.length%2^64) (index : Nat) (inside : index<VarList.decodedCount input (start+last) (total-last)) :
    pointer.toNat≤(VarList.recordPointer input pointer (start+last) index).toNat ∧
    AllocatedBytes.Arena (VarList.recordPointer input pointer (start+last) index)
      (VarList.recordLength input (start+last) (total-last) (VarList.decodedCount input (start+last) (total-last)) index).toNat ∧
    (VarList.recordPointer input pointer (start+last) index).toNat+
      (VarList.recordLength input (start+last) (total-last) (VarList.decodedCount input (start+last) (total-last)) index).toNat≤frontier.toNat ∧
    (VarList.recordLength input (start+last) (total-last) (VarList.decodedCount input (start+last) (total-last)) index).toNat≤input.length%2^64 := by
  obtain ⟨address,bounded,arena,before⟩ := VarList.Records.slice_geometry current input pointer headerArray (start+last) (total-last) inputs.headers index inside
  have codeAddress:=inputs.codeAddress
  have headerAddress:=inputs.headerAddress
  have frontierAddress:=inputs.finalAddress
  refine ⟨by rw [address]; omega,arena,?_,by omega⟩
  have arrayBefore : headerArray.toNat≤frontier.toNat := by omega
  omega

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.Inputs.header_slice_geometry
