import InitECandidate.Solver.Input.MainWitnessPrefix

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes

/-- Exact original heap after the request's80-byte object; witness arrays
remain in the real ordinary arena under the already derived transaction count. -/
theorem witness_geometry (input : Guest.InputBlob) (bounded : input.length % 2^64 ≤ Guest.maxInputBytes)
    (transactions : Payload.transactionCount input ≤ (input.length % 2^64) / 4) :
    (witnessArray input).toNat = DecoderSetup.cursor input + 600 + 16 * Payload.transactionCount input ∧
      (witnessArray input).toNat % 8 = 0 ∧
      inputPointer.toNat + input.length % 2^64 + 8 ≤ (witnessArray input).toNat ∧
      (witnessArray input).toNat + 4 * witnessLength input ≤ 33806089496 ∧
      Arena (RequestPrefix.cursor input) 96 ∧ (RequestPrefix.cursor input).toNat % 8 = 0 ∧
      inputPointer.toNat + input.length % 2^64 + 8 ≤ (RequestPrefix.cursor input).toNat ∧
      (RequestPrefix.cursor input).toNat + 96 ≤ (witnessArray input).toNat := by
  have geometry := input_cursor_bounds input bounded
  have lower : 2713731432 + input.length % 2^64 + 8 ≤ DecoderSetup.cursor input := geometry.1
  have upper : DecoderSetup.cursor input ≤ 2847949152 := geometry.2.1
  have aligned : DecoderSetup.cursor input % 8 = 0 := geometry.2.2
  have small : input.length % 2^64 ≤ 134217712 := bounded
  have previous := PayloadPrefix.final_cursor_geometry input bounded transactions
  have rounding := PersistentAlloc.rounded_nat (PayloadPrefix.finalCursor input) 80#64 (by
    change (PayloadPrefix.finalCursor input).toNat + 80 + 7 < 2^64
    have := previous.2.2.2
    omega)
  have number : (witnessArray input).toNat = (PayloadPrefix.finalCursor input).toNat + 80 := by
    change (witnessArray input).toNat = ((PayloadPrefix.finalCursor input).toNat + 80 + 7) / 8 * 8 at rounding
    have := previous.2.1
    omega
  have siNat : (RequestPrefix.cursor input).toNat = DecoderSetup.cursor input + 288 := by
    rw [RequestPrefix.cursor,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have witnessBound : witnessLength input ≤ input.length % 2^64 := by dsimp only [witnessLength]; omega
  have arrayNat : (witnessArray input).toNat = DecoderSetup.cursor input + 600 + 16 * Payload.transactionCount input := by rw [number,previous.1]; omega
  refine ⟨arrayNat,?_,?_,?_,⟨?_,?_⟩,?_,?_,?_⟩
  · rw [number]; have := previous.2.1; omega
  · change 2713731432 + input.length % 2^64 + 8 ≤ _; rw [arrayNat]; omega
  · rw [arrayNat]; omega
  · rw [siNat]; omega
  · rw [siNat]; omega
  · rw [siNat]; omega
  · change 2713731432 + input.length % 2^64 + 8 ≤ _; rw [siNat]; omega
  · rw [siNat,arrayNat]; omega

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.witness_geometry
