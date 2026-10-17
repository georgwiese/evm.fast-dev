import InitECandidate.Solver.MutableTable.WitnessBuildVariableExecution
import InitECandidate.Solver.Input.VarList.RecordByteBudget
import InitECandidate.Solver.Input.VarList.RecordPointers

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The natural-index view of the actual decoded pointer/length cells. -/
def decodedSlices (input : Guest.InputBlob) (pointer : BitVec 64) (start length index : Nat) : Graph.Slice :=
  (Input.VarList.recordPointer input pointer start index,
   Input.VarList.recordLength input start length (Input.VarList.decodedCount input start length) index)

theorem sliceBytes_prefix (slices : Nat → Graph.Slice) (index count : Nat) :
    sliceBytes slices index count + Input.VarList.sumPrefix (fun i => (slices i).2.toNat) index =
      Input.VarList.sumPrefix (fun i => (slices i).2.toNat) (index + count) := by
  induction count generalizing index with
  | zero => simp [sliceBytes]
  | succ count ih =>
    have rest := ih (index + 1)
    simp only [Input.VarList.sumPrefix] at rest
    change (slices index).2.toNat + sliceBytes slices (index + 1) count +
      Input.VarList.sumPrefix (fun i => (slices i).2.toNat) index = _
    have indices : index + 1 + count = index + (count + 1) := by omega
    rw [indices] at rest
    omega

/-- Normal decoder evidence bounds aggregate hashing bytes once for the
entire original constructor, including zero-length and duplicate records. -/
theorem decoded_whole_price (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length : Nat)
    (records : Input.VarList.Records source input pointer array start length) :
    let count := Input.VarList.decodedCount input start length
    wholeVariablePrice (decodedSlices input pointer start length) count ≤
      215 * count + 7 * triangle count + 20 * ((length - 4 * count) / 136) + 46 := by
  let slices := decodedSlices input pointer start length
  let count := Input.VarList.decodedCount input start length
  have total := sliceBytes_prefix slices 0 count
  simp only [Input.VarList.sumPrefix, Nat.zero_add, Nat.add_zero] at total
  have sizes := Input.VarList.Records.byte_budget source input pointer array start length records
  change Input.VarList.sumPrefix (fun i => (slices i).2.toNat) count + 4 * count ≤ length at sizes
  rw [← total] at sizes
  have byteBound : sliceBytes slices 0 count ≤ length - 4 * count := by omega
  have cost := budget_bytes slices 0 count
  have divided : sliceBytes slices 0 count / 136 ≤ (length - 4 * count) / 136 := Nat.div_le_div_right byteBound
  change wholeVariablePrice slices count ≤
    215 * count + 7 * triangle count + 20 * ((length - 4 * count) / 136) + 46
  unfold wholeVariablePrice
  simp only [Nat.mul_zero, Nat.zero_add] at cost
  omega

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.sliceBytes_prefix
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.decoded_whole_price
