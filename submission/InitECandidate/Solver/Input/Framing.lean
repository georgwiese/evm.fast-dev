import Guest.GasLimit
import Guest.Model
import Mathlib.Data.List.Basic

/-! Direct facts about the challenge's actual host input construction.
There is no bound on the mathematical input-list length in these statements. -/
namespace InitECandidate.Solver.Input.Framing
open Guest

def convert (byte : BitVec 8) : UInt8 := UInt8.ofNat byte.toNat

theorem leBytes_length (word : Word) : (leBytes word).length = 8 := by simp [leBytes]

/-- Beyond the 16-byte frame, host bytes are exactly input bytes, zero beyond
the actual list end. Alignment padding introduces no nonzero data. -/
theorem framed_data (input : InputBlob) (index : Nat) :
    ((hostInputBytes input)[16 + index]?).getD 0 = convert ((input[index]?).getD 0) := by
  let frame := List.replicate 8 (0 : UInt8) ++ leBytes (BitVec.ofNat 64 input.length)
  let padding := List.replicate ((8 - input.length % 8) % 8) (0 : UInt8)
  have frameLength : frame.length = 16 := by simp [frame, leBytes_length]
  have grouped : hostInputBytes input = frame ++ (input.map convert ++ padding) := by
    simp [hostInputBytes, frame, padding, convert, List.append_assoc]
  rw [grouped, List.getElem?_append_right (by rw [frameLength]; omega), frameLength]
  simp only [Nat.add_sub_cancel_left]
  by_cases inside : index < input.length
  · rw [List.getElem?_append_left (by simpa using inside), List.getElem?_map]
    cases h : input[index]? <;> simp [convert, h]
  · have absent : input[index]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [List.getElem?_append_right (by simpa using Nat.le_of_not_gt inside)]
    simp [padding, List.getElem?_replicate, absent, convert]
    split <;> rfl

/-- The framing word is the low 64 bits of input.length, even for mathematical
lists of length at least 2^64. No oversized-list exclusion is introduced. -/
theorem framed_length (input : InputBlob) :
    ((hostInputBytes input).drop 8).take 8 = leBytes (BitVec.ofNat 64 input.length) := by
  simp [hostInputBytes, List.append_assoc, leBytes_length]

/-- A successful execution's fixed container guards identify gas byte 474.
The guards still need to be derived from the actual decoder execution. -/
theorem declared_gas_at_474 (input : InputBlob)
    (request : Guest.GasLimit.le32 input 2 = 16)
    (payload : Guest.GasLimit.le32 input 18 = 44) :
    Guest.GasLimit.declaredGasLimit input = Guest.GasLimit.le64 input 474 := by
  simp [Guest.GasLimit.declaredGasLimit, request, payload]

/-- The framed 64-bit length word always represents length modulo 2^64. -/
theorem framed_length_word (input : InputBlob) :
    (BitVec.ofNat 64 input.length).toNat = input.length % 2 ^ 64 := rfl

/-- The actual shared host-memory function exposes the same byte at every
visible data offset, including zero padding and arbitrary input-list lengths. -/
theorem host_data (input : InputBlob) (index : Nat) (visible : index < maxInputBytes) :
    guestHostMemory input (inputDataAddr + BitVec.ofNat 64 index) =
      some (convert ((input[index]?).getD 0)) := by
  have indexSmall : index < 2 ^ 64 := by dsimp [maxInputBytes] at visible; omega
  have encoded : (BitVec.ofNat 64 index).toNat = index := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexSmall]
  have addressNat : (inputDataAddr + BitVec.ofNat 64 index).toNat = 1073741840 + index := by
    rw [BitVec.toNat_add_of_lt (by
      change 1073741840 + (BitVec.ofNat 64 index).toNat < 2 ^ 64
      rw [encoded]
      dsimp [maxInputBytes] at visible
      omega), encoded]
    rfl
  have inArena : inputAddr ≤ inputDataAddr + BitVec.ofNat 64 index ∧
      inputDataAddr + BitVec.ofNat 64 index < inputAddr + inputArenaSize := by
    change 1073741824 ≤ (inputDataAddr + BitVec.ofNat 64 index).toNat ∧
      (inputDataAddr + BitVec.ofNat 64 index).toNat < 1207959552
    rw [addressNat]
    dsimp [maxInputBytes] at visible
    omega
  have offset : (inputDataAddr + BitVec.ofNat 64 index - inputAddr).toNat = 16 + index := by
    rw [BitVec.toNat_sub_of_le inArena.1, addressNat]
    change 1073741840 + index - 1073741824 = 16 + index
    omega
  simp only [guestHostMemory, inArena, and_self, ↓reduceIte, offset, framed_data]

end InitECandidate.Solver.Input.Framing

#print axioms InitECandidate.Solver.Input.Framing.framed_data
#print axioms InitECandidate.Solver.Input.Framing.framed_length
#print axioms InitECandidate.Solver.Input.Framing.declared_gas_at_474
#print axioms InitECandidate.Solver.Input.Framing.framed_length_word
#print axioms InitECandidate.Solver.Input.Framing.host_data
