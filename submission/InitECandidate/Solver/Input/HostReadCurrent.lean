import InitECandidate.Solver.Input.Framing
import InitECandidate.Solver.Input.SharedReadReached

namespace InitECandidate.Solver.Input.CurrentHostRead
open Flapjack

def dataBytes (input : Guest.InputBlob) (index : Nat) : List UInt8 :=
  (List.range 8).map (fun offset => Framing.convert ((input[index + offset]?).getD 0))

theorem data_word (input : Guest.InputBlob) (index : Nat) :
    Guest.wordOfLeBytes (dataBytes input index) = BitVec.ofNat 64 (Guest.GasLimit.le64 input index) := by
  have convertNat (byte : BitVec 8) : (Framing.convert byte).toNat = byte.toNat := by
    simp [Framing.convert, UInt8.toNat_ofNat', Nat.mod_eq_of_lt byte.isLt]
  unfold Guest.wordOfLeBytes
  apply congrArg (BitVec.ofNat 64)
  simp [dataBytes, List.range_succ, convertNat, Guest.GasLimit.le64,
    Guest.GasLimit.le32, Guest.GasLimit.byte, Nat.add_assoc] <;> omega

/-- Identify a successful current input word read without assuming that later
input words, or padding outside the supplied input, will be readable. -/
theorem normal_reply (input : Guest.InputBlob) (index : Nat)
    (next : Guest.HostMemory) (answer : List (BitVec 8))
    (visible : index + 8 ≤ Guest.maxInputBytes)
    (reply : InitE.sourceOracle (.sharedMem .mappedRead) (Guest.guestHostMemory input) [0#8]
      (panWordToBytesHOL (Guest.inputDataAddr + BitVec.ofNat 64 index) false) = .ret next answer) :
    next = Guest.guestHostMemory input ∧ answer = (dataBytes input index).map byteToBits := by
  have present := SharedRead.oracle_return_present _ next _ answer reply
  have actual := SharedRead.oracle_return_data _ next _ answer reply
  have bytes : SharedRead.bytes (Guest.guestHostMemory input)
      (Guest.inputDataAddr + BitVec.ofNat 64 index) = dataBytes input index := by
    apply List.map_congr_left
    intro offset member
    have inside := List.mem_range.mp member
    have current := present offset inside
    have address : Guest.inputDataAddr + BitVec.ofNat 64 index + BitVec.ofNat 64 offset =
        Guest.inputDataAddr + BitVec.ofNat 64 (index + offset) := by
      rw [BitVec.add_assoc, BitVec.ofNat_add]
    rw [address] at current
    have read := Framing.host_data input (index + offset) (by omega) current
    rw [address, read]
    rfl
  exact ⟨actual.1, by rw [actual.2, bytes]⟩

/-- Decode only the bytes of an observed normal reply. No mathematical-list
size restriction or readability of a later word is assumed. -/
theorem normal_word (input : Guest.InputBlob) (index : Nat)
    (next : Guest.HostMemory) (answer : List (BitVec 8))
    (visible : index + 8 ≤ Guest.maxInputBytes)
    (reply : InitE.sourceOracle (.sharedMem .mappedRead) (Guest.guestHostMemory input) [0#8]
      (panWordToBytesHOL (Guest.inputDataAddr + BitVec.ofNat 64 index) false) = .ret next answer) :
    panWordOfBytesHOL (width := 64) false 0 answer = BitVec.ofNat 64 (Guest.GasLimit.le64 input index) := by
  have actual := normal_reply input index next answer visible reply
  rw [actual.2, WordCodec.pan_word_guest _ (by simp [dataBytes]), data_word]

/-- The actual normal gas-field reply inherits the challenge's 200M limit,
once the actual container offsets have identified that field. -/
theorem normal_gas_word (input : Guest.InputBlob)
    (next : Guest.HostMemory) (answer : List (BitVec 8))
    (request : Guest.GasLimit.le32 input 2 = 16)
    (payload : Guest.GasLimit.le32 input 18 = 44)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000)
    (reply : InitE.sourceOracle (.sharedMem .mappedRead) (Guest.guestHostMemory input) [0#8]
      (panWordToBytesHOL (Guest.inputDataAddr + BitVec.ofNat 64 474) false) = .ret next answer) :
    (panWordOfBytesHOL (width := 64) false 0 answer).toNat ≤ 200000000 := by
  rw [Framing.declared_gas_at_474 input request payload] at gas
  rw [normal_word input 474 next answer (by decide) reply, BitVec.toNat_ofNat]
  exact Nat.le_trans (Nat.mod_le _ _) gas

/-- Connect the real continuing source instruction to the challenge reader,
with arbitrary input-list length and no future-readability premise. -/
theorem reached_word (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (index : Nat) (name : String)
    (expression : Pancake.PanLang.ExpHOL 64) (old : BitVec 64)
    (addressRead : WitnessRadix.QueryBranch.eval source expression =
      some (.val (.word (Guest.inputDataAddr + BitVec.ofNat 64 index))))
    (localPresent : source.locals.lookup (Basis.Pure.MlString.ofString name) = some (.val (.word old)))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle)
    (host : source.ffi.ffiState = Guest.guestHostMemory input)
    (visible : index + 8 ≤ Guest.maxInputBytes)
    (normal : PanSemStateFiniteExact.evaluateHOLFiniteState source
      (.shMemLoad .opW .local (Basis.Pure.MlString.ofString name) expression) = (none, target)) :
    target.locals.lookup (Basis.Pure.MlString.ofString name) =
      some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input index)))) := by
  obtain ⟨mapped, next, answer, reply, cell⟩ :=
    SharedRead.reached_reply source target name expression _ old addressRead localPresent normal
  rw [oracleEq, host] at reply
  rw [normal_word input index next answer visible reply] at cell
  exact cell

set_option maxHeartbeats 200000 in
/-- The real source gas-load continuation contains a bounded gas word. The
field location comes from the two container offsets, not from assumed input
validity or a supplied successful decoder result. -/
theorem reached_gas_word (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (name : String) (expression : Pancake.PanLang.ExpHOL 64) (old : BitVec 64)
    (addressRead : WitnessRadix.QueryBranch.eval source expression =
      some (.val (.word (Guest.inputDataAddr + BitVec.ofNat 64 474))))
    (localPresent : source.locals.lookup (Basis.Pure.MlString.ofString name) = some (.val (.word old)))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle)
    (host : source.ffi.ffiState = Guest.guestHostMemory input)
    (request : Guest.GasLimit.le32 input 2 = 16)
    (payload : Guest.GasLimit.le32 input 18 = 44)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000)
    (normal : PanSemStateFiniteExact.evaluateHOLFiniteState source
      (.shMemLoad .opW .local (Basis.Pure.MlString.ofString name) expression) = (none, target)) :
    ∃ value : BitVec 64, value.toNat ≤ 200000000 ∧
      target.locals.lookup (Basis.Pure.MlString.ofString name) = some (.val (.word value)) := by
  have cell := reached_word source target input 474 name expression old addressRead localPresent
    oracleEq host (by decide) normal
  refine ⟨BitVec.ofNat 64 (Guest.GasLimit.le64 input 474), ?_, cell⟩
  rw [Framing.declared_gas_at_474 input request payload] at gas
  rw [BitVec.toNat_ofNat]
  exact Nat.le_trans (Nat.mod_le (Guest.GasLimit.le64 input 474) (2 ^ 64)) gas

end InitECandidate.Solver.Input.CurrentHostRead

#print axioms InitECandidate.Solver.Input.CurrentHostRead.normal_reply
#print axioms InitECandidate.Solver.Input.CurrentHostRead.data_word
#print axioms InitECandidate.Solver.Input.CurrentHostRead.normal_word
#print axioms InitECandidate.Solver.Input.CurrentHostRead.normal_gas_word
#print axioms InitECandidate.Solver.Input.CurrentHostRead.reached_word
#print axioms InitECandidate.Solver.Input.CurrentHostRead.reached_gas_word
