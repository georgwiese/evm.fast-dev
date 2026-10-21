import InitECandidate.Solver.Input.MainPayloadHashData
import InitECandidate.Solver.Input.VarList.RecordGeometry

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.Main.PayloadHashData
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The full hasher input/record geometry follows from actual normal main
decoding and its real prehash heap frontier. Zero transaction arrays remain
unmapped sentinels; every positive array and every input slice is derived. -/
theorem layout (input : Guest.InputBlob) (caller current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (actual : DecoderCall.DecoderReady input caller current) (bounded : input.length%2^64≤Guest.maxInputBytes)
    (after : (DecoderCall.witnessArray input).toNat≤root.toNat) :
    (description input).Layout inputPointer.toNat root.toNat (input.length%2^64) := by
  have inputBound : input.length%2^64≤134217712 := bounded
  have inputNumber : inputPointer.toNat=2713731432 := rfl
  have numbers := input_cursor_bounds input bounded
  have decodedLower : inputPointer.toNat+input.length%2^64+8≤DecoderSetup.cursor input := numbers.1
  have decodedUpper : DecoderSetup.cursor input≤2847949152 := numbers.2.1
  have decodedAligned : DecoderSetup.cursor input%8=0 := numbers.2.2
  have payloadNumber := PayloadPrefix.cursor_number input bounded
  have countBound := VarList.Records.count_input_bound current input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64)
    (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) actual.records
  change Payload.transactionCount input≤(input.length%2^64)/4 at countBound
  have witnessNumber := (DecoderCall.witness_geometry input bounded countBound).1
  have lengthNumber : (PayloadPrefix.length input).toNat=Guest.GasLimit.le32 input 22-44 := by
    rw [PayloadPrefix.length,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    have h:=RawScalar.le32_lt input 22; omega
  have ranges := actual.payloadLayout.ranges input (PayloadPrefix.length input)
  have inside : 62+(PayloadPrefix.length input).toNat≤input.length%2^64 := by
    have a:=actual.layout.extent; have b:=actual.layout.payloadLower; have c:=actual.layout.offsetsOrdered
    have d:=actual.layout.hashesUpper; have e:=actual.layout.requestUpper
    rw [lengthNumber]; omega
  have transactionBound := (RequestHash.parsed_byte_budget input caller current actual).1
  have transactionLength := VarList.Records.size_bounds current input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64)
    (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) actual.records
  have transactionInputs := VarList.Records.slice_geometry current input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64)
    (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) actual.records
  have arrayNumber : (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64).toNat=DecoderSetup.cursor input+520 := by
    have rounded := PersistentAlloc.rounded_nat (PayloadPrefix.cursor input) 136#64 (by change (PayloadPrefix.cursor input).toNat+136+7<2^64; rw [payloadNumber.1]; omega)
    rw [payloadNumber.1] at rounded
    change _=((DecoderSetup.cursor input+384+136+7)/8*8) at rounded
    have aligned:=numbers.2.2
    omega
  have inputArena : AllocatedBytes.Arena inputPointer (input.length%2^64) := ⟨by decide,by change 2713731432+input.length%2^64≤33806089496; omega⟩
  have withdrawalPointer : (description input).withdrawals=inputPointer+BitVec.ofNat 64 (62+Guest.GasLimit.le32 input 570) := by
    change inputPointer+62#64+BitVec.ofNat 64 (Guest.GasLimit.le32 input 570)=_
    rw [BitVec.ofNat_add,←BitVec.add_assoc]
  have balancePointer : (description input).balance=inputPointer+BitVec.ofNat 64 (62+Guest.GasLimit.le32 input 590) := by
    change inputPointer+62#64+BitVec.ofNat 64 (Guest.GasLimit.le32 input 590)=_
    rw [BitVec.ofNat_add,←BitVec.add_assoc]
  have balanceLength : (description input).balanceLength=(PayloadPrefix.length input).toNat-Guest.GasLimit.le32 input 590 := actual.payloadLayout.balance_length input (PayloadPrefix.length input)
  have arrayPositive (positive : 0<(description input).transactionCount) : Payload.transactionBytes input≠0 := by
    intro zero
    change 0<Payload.transactionCount input at positive
    simp [Payload.transactionCount,VarList.decodedCount,zero] at positive
  refine {
    budgetBound := by omega
    payloadArena := ?_
    payloadAligned := payloadNumber.2
    payloadLower := ?_
    payloadBefore := ?_
    rawArena := ?_
    extraShort := actual.payloadLayout.extra
    extraArena := ?_
    transactionCountBound := countBound
    transactionArena := ?_
    transactionAligned := ?_
    transactionLower := ?_
    transactionBefore := ?_
    transactionLengths := ?_
    transactionInputs := ?_
    transactionBytes := ?_
    withdrawalCountBound := ?_
    withdrawalArena := ?_
    balanceBound := ?_
    balanceArena := ?_
  }
  · exact ⟨by change 2701131776≤(PayloadPrefix.cursor input).toNat; rw [payloadNumber.1]; omega,
      by change (PayloadPrefix.cursor input).toNat+136≤33806089496; rw [payloadNumber.1]; have h:=numbers.2.1; omega⟩
  · change inputPointer.toNat≤(PayloadPrefix.cursor input).toNat
    rw [payloadNumber.1]; have h:=numbers.1; omega
  · change (PayloadPrefix.cursor input).toNat+136≤root.toNat
    rw [payloadNumber.1]; omega
  · exact AllocatedBytes.Arena.subrange inputPointer (input.length%2^64) 62 540 inputArena (by omega)
  · exact AllocatedBytes.Arena.subrange inputPointer (input.length%2^64) 602 (Guest.GasLimit.le32 input 566-540) inputArena (by omega)
  · intro positive
    change AllocatedBytes.Arena (VarList.decodedArray _ (Payload.transactionBytes input)) (16*Payload.transactionCount input)
    rw [VarList.decodedArray,if_neg (arrayPositive positive)]
    exact ⟨by rw [arrayNumber]; have h:=numbers.1; omega,by rw [arrayNumber]; have h:=numbers.2.1; omega⟩
  · change (VarList.decodedArray _ (Payload.transactionBytes input)).toNat%8=0
    by_cases zero : Payload.transactionBytes input=0
    · simp only [VarList.decodedArray,if_pos zero]; decide
    · rw [VarList.decodedArray,if_neg zero,arrayNumber]; have h:=numbers.2.2; omega
  · intro positive
    change inputPointer.toNat≤(VarList.decodedArray _ (Payload.transactionBytes input)).toNat
    rw [VarList.decodedArray,if_neg (arrayPositive positive),arrayNumber]; have h:=numbers.1; omega
  · intro positive
    change (VarList.decodedArray _ (Payload.transactionBytes input)).toNat+16*Payload.transactionCount input≤root.toNat
    rw [VarList.decodedArray,if_neg (arrayPositive positive),arrayNumber]; omega
  · intro index active
    exact Nat.le_trans (transactionLength.2 index active) (Nat.le_trans (Nat.le_add_right _ _) transactionBound)
  · intro index active
    exact (transactionInputs index active).2.2.1
  · exact Nat.le_trans transactionLength.1 (Nat.le_trans (Nat.le_add_right _ _) transactionBound)
  · exact Payload.withdrawal_count_bound input (PayloadPrefix.length input) actual.payloadLayout.valid inside
  · rw [withdrawalPointer]
    exact AllocatedBytes.Arena.subrange inputPointer (input.length%2^64) (62+Guest.GasLimit.le32 input 570) (44*Payload.withdrawalCount input) inputArena
      (by unfold Payload.withdrawalCount; omega)
  · rw [balanceLength]; omega
  · rw [balancePointer,balanceLength]
    exact AllocatedBytes.Arena.subrange inputPointer (input.length%2^64) (62+Guest.GasLimit.le32 input 590) ((PayloadPrefix.length input).toNat-Guest.GasLimit.le32 input 590) inputArena (by omega)

end InitECandidate.Solver.Input.Main.PayloadHashData
#print axioms InitECandidate.Solver.Input.Main.PayloadHashData.layout
