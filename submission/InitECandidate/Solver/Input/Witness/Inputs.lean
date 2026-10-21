import InitECandidate.Solver.Input.Witness.BodyNormalPadded

namespace InitECandidate.Solver.Input.Witness
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Current decoded witness records and original allocation snapshot. The
frontier records the decoder's allocation end; later heap globals may move. -/
structure Inputs (current : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array si codeArray headerArray frontier : BitVec 64) (start first middle last total : Nat) : Prop where
  nodes : VarList.Records current input pointer array (start+first) (middle-first)
  codes : VarList.Records current input pointer codeArray (start+middle) (last-middle)
  headers : VarList.Records current input pointer headerArray (start+last) (total-last)
  nodeSizes : ∀ index<VarList.decodedCount input (start+first) (middle-first),
    (VarList.recordLength input (start+first) (middle-first) (VarList.decodedCount input (start+first) (middle-first)) index).toNat≤1024
  codeSizes : ∀ index<VarList.decodedCount input (start+middle) (last-middle),
    (VarList.recordLength input (start+middle) (last-middle) (VarList.decodedCount input (start+middle) (last-middle)) index).toNat≤65536
  headerCount : VarList.decodedCount input (start+last) (total-last)≤256
  bytes : Blob.HeapInput current input pointer
  nodePointer : current.memory (byteAddress si 40)=.word (VarList.decodedArray array (middle-first))
  nodeCount : current.memory (byteAddress si 48)=.word (BitVec.ofNat 64 (VarList.decodedCount input (start+first) (middle-first)))
  codePointer : current.memory (byteAddress si 56)=.word (VarList.decodedArray codeArray (last-middle))
  codeCount : current.memory (byteAddress si 64)=.word (BitVec.ofNat 64 (VarList.decodedCount input (start+middle) (last-middle)))
  headerPointer : current.memory (byteAddress si 72)=.word (VarList.decodedArray headerArray (total-last))
  headerCountCell : current.memory (byteAddress si 80)=.word (BitVec.ofNat 64 (VarList.decodedCount input (start+last) (total-last)))
  codeAddress : codeArray.toNat=array.toNat+16*VarList.decodedCount input (start+first) (middle-first)
  headerAddress : headerArray.toNat=codeArray.toNat+16*VarList.decodedCount input (start+middle) (last-middle)
  codeAligned : codeArray.toNat%8=0
  headerAligned : headerArray.toNat%8=0
  finalAddress : frontier.toNat=array.toNat+16*(VarList.decodedCount input (start+first) (middle-first)+
    VarList.decodedCount input (start+middle) (last-middle)+VarList.decodedCount input (start+last) (total-last))
  finalBound : frontier.toNat≤array.toNat+4*total
  finalAligned : frontier.toNat%8=0

/-- Actual normal witness decoding supplies the input snapshot together
with its then-current heap global. The facts remain explicitly separate. -/
theorem inputs_of_decoded (current : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array si : BitVec 64) (start first middle last total : Nat) (value : ValueHOL 64)
    (actual : Decoded current input pointer array si start first middle last total value) :
    ∃ codeArray headerArray frontier,value=.val (.word si) ∧ Inputs current input pointer array si codeArray headerArray frontier start first middle last total ∧
      current.globals.lookup (ofString "heap_ptr")=some (.val (.word frontier)) := by
  obtain ⟨codeArray,headerArray,frontier,returned,nodes,codes,headers,nodeSizes,codeSizes,headerCount,bytes,nodePointer,nodeCount,codePointer,codeCount,headerPointer,headerCountCell,
    heap,codeAddress,headerAddress,codeAligned,headerAligned,finalAddress,finalBound,finalAligned⟩ := actual
  exact ⟨codeArray,headerArray,frontier,returned,
    ⟨nodes,codes,headers,nodeSizes,codeSizes,headerCount,bytes,nodePointer,nodeCount,codePointer,codeCount,headerPointer,headerCountCell,
      codeAddress,headerAddress,codeAligned,headerAligned,finalAddress,finalBound,finalAligned⟩,heap⟩

end InitECandidate.Solver.Input.Witness
#print axioms InitECandidate.Solver.Input.Witness.inputs_of_decoded
