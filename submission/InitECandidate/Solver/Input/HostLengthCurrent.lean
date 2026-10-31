import InitECandidate.Solver.Input.Framing
import InitECandidate.Solver.Input.SharedReadReached

namespace InitECandidate.Solver.Input.CurrentHostLength
open Flapjack

theorem framed_byte (input : Guest.InputBlob) (index : Nat) (inside : index < 8) :
    ((Guest.hostInputBytes input)[8 + index]?).getD 0 =
      ((Guest.leBytes (BitVec.ofNat 64 input.length))[index]?).getD 0 := by
  let data := input.map (fun byte => UInt8.ofNat byte.toNat) ++
    List.replicate ((8 - input.length % 8) % 8) 0
  have grouped : Guest.hostInputBytes input = List.replicate 8 0 ++
      (Guest.leBytes (BitVec.ofNat 64 input.length) ++ data) := by
    simp [Guest.hostInputBytes, data, List.append_assoc]
  rw [grouped, List.getElem?_append_right (by simp)]
  simp only [List.length_replicate, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa [Guest.leBytes] using inside)]

/-- Identify a present length-header byte. The arbitrary mathematical list
may overflow the host's word-sized backing extent, so presence is observed. -/
theorem host_byte (input : Guest.InputBlob) (index : Nat) (inside : index < 8)
    (present : (Guest.guestHostMemory input (Guest.inputLenAddr + BitVec.ofNat 64 index)).isSome = true) :
    Guest.guestHostMemory input (Guest.inputLenAddr + BitVec.ofNat 64 index) =
      some (((Guest.leBytes (BitVec.ofNat 64 input.length))[index]?).getD 0) := by
  have encoded : (BitVec.ofNat 64 index).toNat = index := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have addressNat : (Guest.inputLenAddr + BitVec.ofNat 64 index).toNat = 1073741832 + index := by
    rw [BitVec.toNat_add_of_lt (by
      change 1073741832 + (BitVec.ofNat 64 index).toNat < 2^64
      rw [encoded]
      omega), encoded]
    rfl
  have lower : Guest.inputAddr ≤ Guest.inputLenAddr + BitVec.ofNat 64 index := by
    change 1073741824 ≤ (Guest.inputLenAddr + BitVec.ofNat 64 index).toNat
    rw [addressNat]
    omega
  have notOutput : ¬ (Guest.outputAddr ≤ Guest.inputLenAddr + BitVec.ofNat 64 index ∧
      Guest.inputLenAddr + BitVec.ofNat 64 index < Guest.outputEnd) := by
    intro output
    have first := output.1
    change 2688614400 ≤ (Guest.inputLenAddr + BitVec.ofNat 64 index).toNat at first
    rw [addressNat] at first
    omega
  have offset : (Guest.inputLenAddr + BitVec.ofNat 64 index - Guest.inputAddr).toNat = 8 + index := by
    rw [BitVec.toNat_sub_of_le lower, addressNat]
    change 1073741832 + index - 1073741824 = 8 + index
    omega
  by_cases backed : Guest.inputLenAddr + BitVec.ofNat 64 index <
      Guest.inputAddr + BitVec.ofNat 64 (Guest.hostInputBytes input).length
  · simp only [Guest.guestHostMemory, lower, backed, and_self, ↓reduceIte, offset] at present ⊢
    cases read : (Guest.hostInputBytes input)[8 + index]? with
    | none => simp [read] at present
    | some byte =>
      have value := framed_byte input index inside
      rw [read] at value
      simpa only [read, Option.getD_some] using congrArg some value
  · simp only [Guest.guestHostMemory, lower, backed, and_false, ↓reduceIte,
      notOutput, Option.isSome_none, Bool.false_eq_true] at present

theorem present_bytes (input : Guest.InputBlob)
    (present : ∀ offset < 8, (Guest.guestHostMemory input
      (Guest.inputLenAddr + BitVec.ofNat 64 offset)).isSome = true) :
    SharedRead.bytes (Guest.guestHostMemory input) Guest.inputLenAddr =
      Guest.leBytes (BitVec.ofNat 64 input.length) := by
  apply List.ext_getElem
  · simp [SharedRead.bytes, Guest.leBytes]
  · intro index left right
    have inside : index < 8 := by simpa [SharedRead.bytes] using left
    simp only [SharedRead.bytes, List.getElem_map, List.getElem_range]
    rw [host_byte input index inside (present index inside), List.getElem?_eq_getElem right]
    rfl

theorem normal_word (input : Guest.InputBlob) (next : Guest.HostMemory) (answer : List (BitVec 8))
    (reply : InitE.sourceOracle (.sharedMem .mappedRead) (Guest.guestHostMemory input) [0#8]
      (panWordToBytesHOL Guest.inputLenAddr false) = .ret next answer) :
    panWordOfBytesHOL (width := 64) false 0 answer = BitVec.ofNat 64 input.length := by
  have present := SharedRead.oracle_return_present _ next _ answer reply
  have actual := SharedRead.oracle_return_data _ next _ answer reply
  rw [actual.2, present_bytes input present, WordCodec.pan_word_guest _ (by simp [Guest.leBytes]),
    WordCodec.guest_roundtrip]

/-- An actual continuing length-load instruction contains the low 64 bits of
the mathematical list length. No size, backing, mapping or future-read premise. -/
theorem reached_word (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (name : String) (expression : Pancake.PanLang.ExpHOL 64) (old : BitVec 64)
    (addressRead : WitnessRadix.QueryBranch.eval source expression = some (.val (.word Guest.inputLenAddr)))
    (localPresent : source.locals.lookup (Basis.Pure.MlString.ofString name) = some (.val (.word old)))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle)
    (host : source.ffi.ffiState = Guest.guestHostMemory input)
    (normal : PanSemStateFiniteExact.evaluateHOLFiniteState source
      (.shMemLoad .opW .local (Basis.Pure.MlString.ofString name) expression) = (none, target)) :
    target.locals.lookup (Basis.Pure.MlString.ofString name) =
      some (.val (.word (BitVec.ofNat 64 input.length))) := by
  obtain ⟨mapped, next, answer, reply, cell⟩ := SharedRead.reached_reply source target name expression
    Guest.inputLenAddr old addressRead localPresent normal
  rw [oracleEq, host] at reply
  rw [normal_word input next answer reply] at cell
  exact cell

end InitECandidate.Solver.Input.CurrentHostLength

#print axioms InitECandidate.Solver.Input.CurrentHostLength.framed_byte
#print axioms InitECandidate.Solver.Input.CurrentHostLength.host_byte
#print axioms InitECandidate.Solver.Input.CurrentHostLength.present_bytes
#print axioms InitECandidate.Solver.Input.CurrentHostLength.normal_word
#print axioms InitECandidate.Solver.Input.CurrentHostLength.reached_word
