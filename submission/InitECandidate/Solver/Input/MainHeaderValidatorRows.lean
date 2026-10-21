import InitECandidate.Solver.Input.MainHeaderSlices
import InitECandidate.Solver.Headers.ValidateRowsFromRecords
import InitECandidate.Solver.Input.VarList.RecordByteBudget

namespace InitECandidate.Solver.Input.Main.HeaderSlices
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Main's actual post-hash SSZ rows satisfy the original validator's
physical row contract and shared encoded-byte budget. The genuine SI
pointer/count cells and empty-list convention are retained. -/
theorem validator_rows_after_hash (input : Guest.InputBlob) (before copiedSource origin current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts) (returned : RequestHash.Returned input origin current root) :
    count input≤256 ∧ Rlp.Validation.Arena current 2713714688#64 2701135872#64 ∧
      ∃ headerArray,Headers.Validate.Rows current (VarList.decodedArray headerArray (bytes input)) (pointer input) (length input) (count input)
        inputPointer.toNat (PersistentAlloc.rounded root 32#64).toNat ∧
      current.memory (byteAddress (RequestPrefix.cursor input) 72)=.word (VarList.decodedArray headerArray (bytes input)) ∧
      current.memory (byteAddress (RequestPrefix.cursor input) 80)=.word (BitVec.ofNat 64 (count input)) ∧
      VarList.sumPrefix (fun index=>(length input index).toNat) (count input)+4*count input≤input.length%2^64 := by
  obtain ⟨small,arena,codeArray,headerArray,inputs,geometry⟩ := after_hash input before copiedSource origin current root counts copied actual bounded prepared returned
  have endBefore : headerArray.toNat+16*count input≤root.toNat := by
    have final:=inputs.finalAddress
    have code:=inputs.codeAddress
    have header:=inputs.headerAddress
    change headerArray.toNat=codeArray.toNat+16*VarList.decodedCount input (DecoderCall.witnessStart input+Witness.offsetNat input (DecoderCall.witnessStart input) 1)
      (Witness.offsetNat input (DecoderCall.witnessStart input) 2-Witness.offsetNat input (DecoderCall.witnessStart input) 1) at header
    change root.toNat=(DecoderCall.witnessArray input).toNat+16*(VarList.decodedCount input _ _+VarList.decodedCount input _ _+count input) at final
    omega
  have byteBound : bytes input≤input.length%2^64 := by unfold bytes DecoderCall.witnessLength; omega
  have inputBound : input.length%2^64≤134217712 := bounded
  have rows : Headers.Validate.Rows current (VarList.decodedArray headerArray (bytes input)) (pointer input) (length input) (count input)
      inputPointer.toNat (PersistentAlloc.rounded root 32#64).toNat := by
    by_cases empty : bytes input=0
    · have zeroCount : count input=0 := by simp [count,VarList.decodedCount,empty]
      rw [zeroCount]
      constructor <;> simp
    · have arrayGeometry:=inputs.headers.array_geometry current input inputPointer headerArray (start input) (bytes input) empty
      exact Headers.Validate.Rows.of_records current input inputPointer headerArray (start input) (bytes input) inputPointer.toNat (PersistentAlloc.rounded root 32#64).toNat
        inputs.headers arena.domain (Nat.le_refl _) (by have after:=arrayGeometry.2.2.2.2; omega)
        (endBefore.trans prepared.before) (by omega)
  have budget:=inputs.headers.byte_budget current input inputPointer headerArray (start input) (bytes input)
  change VarList.sumPrefix (fun index=>(length input index).toNat) (count input)+4*count input≤bytes input at budget
  exact ⟨small,arena,headerArray,rows,inputs.headerPointer,inputs.headerCountCell,by omega⟩

end InitECandidate.Solver.Input.Main.HeaderSlices

#print axioms InitECandidate.Solver.Input.Main.HeaderSlices.validator_rows_after_hash
