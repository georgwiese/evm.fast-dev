import InitECandidate.Solver.Input.MainWitnessHashInputs
import InitECandidate.Solver.Input.MainScratchArena
import InitECandidate.Solver.Input.Witness.HeaderGeometry
import InitECandidate.Solver.Headers.DecodeEntryTrace

namespace InitECandidate.Solver.Input.Main.HeaderSlices
open Flapjack PanSemStateFiniteExact WitnessRadix

def start (input : Guest.InputBlob) := DecoderCall.witnessStart input+Witness.offsetNat input (DecoderCall.witnessStart input) 2
def bytes (input : Guest.InputBlob) := DecoderCall.witnessLength input-Witness.offsetNat input (DecoderCall.witnessStart input) 2
def count (input : Guest.InputBlob) := VarList.decodedCount input (start input) (bytes input)
def pointer (input : Guest.InputBlob) (index : Nat) := VarList.recordPointer input inputPointer (start input) index
def length (input : Guest.InputBlob) (index : Nat) := VarList.recordLength input (start input) (bytes input) (count input) index

/-- Main's real post-hash header inputs satisfy the original header
parser's byte/arena geometry. This retains the physical decoder snapshot,
all SI/record cells and the original scratch cursors; later validate_headers
allocations and preceding iterations still need their actual frames. -/
theorem after_hash (input : Guest.InputBlob) (before copiedSource origin current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts) (returned : RequestHash.Returned input origin current root) :
    count input≤256 ∧ Rlp.Validation.Arena current 2713714688#64 2701135872#64 ∧
      ∃ codeArray headerArray,
        Witness.Inputs current input inputPointer (DecoderCall.witnessArray input) (RequestPrefix.cursor input) codeArray headerArray root
          (DecoderCall.witnessStart input) (Witness.offsetNat input (DecoderCall.witnessStart input) 0) (Witness.offsetNat input (DecoderCall.witnessStart input) 1)
          (Witness.offsetNat input (DecoderCall.witnessStart input) 2) (DecoderCall.witnessLength input) ∧
        ∀ index<count input,inputPointer.toNat≤(pointer input index).toNat ∧ AllocatedBytes.Arena (pointer input index) (length input index).toNat ∧
          (pointer input index).toNat+(length input index).toNat≤(PersistentAlloc.rounded root 32#64).toNat ∧
          (length input index).toNat≤input.length%2^64 ∧ 16*(length input index).toNat<2^64 := by
  obtain ⟨codeArray,headerArray,inputs⟩ := witness_inputs_after_hash input (DecoderSetup.entered copiedSource input) origin current root counts actual bounded prepared returned
  have arena:=ScratchArena.after_hash_arena input before copiedSource origin current root copied actual returned
  have witnessBound : DecoderCall.witnessLength input≤input.length%2^64 := by unfold DecoderCall.witnessLength; omega
  refine ⟨inputs.headerCount,arena.1,codeArray,headerArray,inputs,?_⟩
  intro index inside
  obtain ⟨afterInput,sliceArena,beforeFrontier,size⟩ := inputs.header_slice_geometry current input inputPointer (DecoderCall.witnessArray input) (RequestPrefix.cursor input) codeArray headerArray root
    (DecoderCall.witnessStart input) (Witness.offsetNat input (DecoderCall.witnessStart input) 0) (Witness.offsetNat input (DecoderCall.witnessStart input) 1)
    (Witness.offsetNat input (DecoderCall.witnessStart input) 2) (DecoderCall.witnessLength input) witnessBound index inside
  change inputPointer.toNat≤(pointer input index).toNat at afterInput
  change AllocatedBytes.Arena (pointer input index) (length input index).toNat at sliceArena
  change (pointer input index).toNat+(length input index).toNat≤root.toNat at beforeFrontier
  change (length input index).toNat≤input.length%2^64 at size
  have inputBound : input.length%2^64≤134217712 := bounded
  exact ⟨afterInput,sliceArena,beforeFrontier.trans prepared.before,size,by omega⟩

end InitECandidate.Solver.Input.Main.HeaderSlices

#print axioms InitECandidate.Solver.Input.Main.HeaderSlices.after_hash
