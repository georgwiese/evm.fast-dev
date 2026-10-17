import InitECandidate.Solver.Input.Framing

namespace InitECandidate.Solver.Input.HostGas
open Guest

/-- Read from the actual initial shared-memory function, not a decoder mirror. -/
def byte (input : InputBlob) (index : Nat) : Nat :=
  ((guestHostMemory input (inputDataAddr + BitVec.ofNat 64 index)).getD 0).toNat

theorem byte_eq (input : InputBlob) (index : Nat) (visible : index < maxInputBytes) :
    byte input index = Guest.GasLimit.byte input index := by
  unfold byte
  rw [Framing.host_data input index visible]
  have small := ((input[index]?).getD 0).isLt
  simp [Guest.GasLimit.byte, Framing.convert, UInt8.toNat_ofNat', Nat.mod_eq_of_lt small]

theorem byte_lt (input : InputBlob) (index : Nat) : byte input index < 256 :=
  UInt8.toNat_lt_size _

def le32 (input : InputBlob) (index : Nat) : Nat :=
  byte input index + byte input (index + 1) * 256 + byte input (index + 2) * 65536 +
    byte input (index + 3) * 16777216

def le64 (input : InputBlob) (index : Nat) : Nat :=
  le32 input index + le32 input (index + 4) * 4294967296

theorem le32_eq (input : InputBlob) (index : Nat) (visible : index + 3 < maxInputBytes) :
    le32 input index = Guest.GasLimit.le32 input index := by
  unfold le32 Guest.GasLimit.le32
  rw [byte_eq input index (by omega), byte_eq input (index + 1) (by omega),
    byte_eq input (index + 2) (by omega), byte_eq input (index + 3) visible]

theorem le64_eq (input : InputBlob) (index : Nat) (visible : index + 7 < maxInputBytes) :
    le64 input index = Guest.GasLimit.le64 input index := by
  unfold le64 Guest.GasLimit.le64
  rw [le32_eq input index (by omega), le32_eq input (index + 4) (by omega)]

theorem le32_lt (input : InputBlob) (index : Nat) : le32 input index < 2 ^ 32 := by
  have h0 := byte_lt input index
  have h1 := byte_lt input (index + 1)
  have h2 := byte_lt input (index + 2)
  have h3 := byte_lt input (index + 3)
  unfold le32
  omega

theorem le64_lt (input : InputBlob) (index : Nat) : le64 input index < 2 ^ 64 := by
  have first := le32_lt input index
  have second := le32_lt input (index + 4)
  unfold le64
  omega

/-- The two successful container guards suffice to connect the challenge gas
premise to the initial host's eight payload bytes. No input-length premise. -/
theorem declared_eq_host_field (input : InputBlob)
    (request : le32 input 2 = 16) (payload : le32 input 18 = 44) :
    Guest.GasLimit.declaredGasLimit input = le64 input 474 := by
  have requestEq := le32_eq input 2 (by decide)
  have payloadEq := le32_eq input 18 (by decide)
  have requestFixed : Guest.GasLimit.le32 input 2 = 16 := requestEq.symm.trans request
  have payloadFixed : Guest.GasLimit.le32 input 18 = 44 := payloadEq.symm.trans payload
  rw [Framing.declared_gas_at_474 input requestFixed payloadFixed,
    le64_eq input 474 (by decide)]

theorem host_field_bound (input : InputBlob)
    (request : le32 input 2 = 16) (payload : le32 input 18 = 44)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
    le64 input 474 ≤ 200000000 := by
  rw [← declared_eq_host_field input request payload]
  exact gas

/-- Packing the eight host bytes into the actual 64-bit gas word cannot wrap. -/
theorem host_word_bound (input : InputBlob)
    (request : le32 input 2 = 16) (payload : le32 input 18 = 44)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
    (BitVec.ofNat 64 (le64 input 474)).toNat ≤ 200000000 := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (le64_lt input 474)]
  exact host_field_bound input request payload gas

end InitECandidate.Solver.Input.HostGas

#print axioms InitECandidate.Solver.Input.HostGas.byte_eq
#print axioms InitECandidate.Solver.Input.HostGas.declared_eq_host_field
#print axioms InitECandidate.Solver.Input.HostGas.host_word_bound
