import InitECandidate.Solver.Input.Witness.BodyNormal
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- Physical records, validated sizes and actual SI fields of the original witness. -/
def Decoded (post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array si : BitVec 64) (start first middle last total : Nat) (value : ValueHOL 64) : Prop :=
    ∃ codeArray headerArray finalCursor : BitVec 64,
      value=.val (.word si) ∧
      VarList.Records post input pointer array (start+first) (middle-first) ∧
      VarList.Records post input pointer codeArray (start+middle) (last-middle) ∧
      VarList.Records post input pointer headerArray (start+last) (total-last) ∧
      (∀ index<VarList.decodedCount input (start+first) (middle-first),
        (VarList.recordLength input (start+first) (middle-first) (VarList.decodedCount input (start+first) (middle-first)) index).toNat≤1024) ∧
      (∀ index<VarList.decodedCount input (start+middle) (last-middle),
        (VarList.recordLength input (start+middle) (last-middle) (VarList.decodedCount input (start+middle) (last-middle)) index).toNat≤65536) ∧
      VarList.decodedCount input (start+last) (total-last)≤256 ∧ Blob.HeapInput post input pointer ∧
      post.memory (byteAddress si 40)=.word (VarList.decodedArray array (middle-first)) ∧
      post.memory (byteAddress si 48)=.word (BitVec.ofNat 64 (VarList.decodedCount input (start+first) (middle-first))) ∧
      post.memory (byteAddress si 56)=.word (VarList.decodedArray codeArray (last-middle)) ∧
      post.memory (byteAddress si 64)=.word (BitVec.ofNat 64 (VarList.decodedCount input (start+middle) (last-middle))) ∧
      post.memory (byteAddress si 72)=.word (VarList.decodedArray headerArray (total-last)) ∧
      post.memory (byteAddress si 80)=.word (BitVec.ofNat 64 (VarList.decodedCount input (start+last) (total-last))) ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalCursor)) ∧
      codeArray.toNat=array.toNat+16*VarList.decodedCount input (start+first) (middle-first) ∧
      headerArray.toNat=codeArray.toNat+16*VarList.decodedCount input (start+middle) (last-middle) ∧
      codeArray.toNat%8=0 ∧ headerArray.toNat%8=0 ∧
      finalCursor.toNat=array.toNat+16*(VarList.decodedCount input (start+first) (middle-first)+
        VarList.decodedCount input (start+middle) (last-middle)+VarList.decodedCount input (start+last) (total-last)) ∧
      finalCursor.toNat≤array.toNat+4*total ∧ finalCursor.toNat%8=0

theorem decoded_of_arrays (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array si : BitVec 64) (start first middle last total : Nat) (value : ValueHOL 64)
    (actual : ArraysResult source post input pointer array si start first middle last total value) :
    Decoded post input pointer array si start first middle last total value := by
  obtain ⟨codeArray,headerArray,finalCursor,returned,nodes,codes,headers,nodeSizes,codeSizes,headerCount,bytes,nodePointer,nodeCount,codePointer,codeCount,headerPointer,headerCountCell,heapCursor,codeAddress,headerAddress,codeAligned,headerAligned,finalAddress,finalBound,finalAligned,clockLower,clockUpper⟩ := actual
  exact ⟨codeArray,headerArray,finalCursor,returned,nodes,codes,headers,nodeSizes,codeSizes,headerCount,bytes,nodePointer,nodeCount,codePointer,codeCount,headerPointer,headerCountCell,heapCursor,codeAddress,headerAddress,codeAligned,headerAligned,finalAddress,finalBound,finalAligned⟩

theorem body_normal_any_clock (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer offsetArray array si : BitVec 64) (start total : Nat)
    (environment : Environment source) (heap : Blob.HeapInput source input pointer)
    (minimum : 12≤total) (inside : start+total≤input.length%2^64)
    (wp : source.locals.lookup (ofString "wp")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (wlen : source.locals.lookup (ofString "wlen")=some (.val (.word (BitVec.ofNat 64 total))))
    (offsets : source.globals.lookup (ofString "ssz_offs")=some (.val (.word offsetArray)))
    (pointerLower : 2701131776≤pointer.toNat) (pointerAligned : pointer.toNat%8=0)
    (offsetAligned : offsetArray.toNat%8=0) (offsetLower : 2701131776≤offsetArray.toNat)
    (offsetBefore : offsetArray.toNat+24≤pointer.toNat)
    (arrayAligned : array.toNat%8=0) (arrayAfter : pointer.toNat+input.length%2^64+8≤array.toNat)
    (room : array.toNat+4*total≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word array)))
    (offsetCode : source.code.lookup (ofString "ssz_check_offsets")=some (Offsets.formals,Offsets.body,.one))
    (siLocal : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (siArena : Arena si 96) (siAligned : si.toNat%8=0) (siAfter : pointer.toNat+input.length%2^64+8≤si.toNat)
    (siBefore : si.toNat+96≤array.toNat)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source offsetBody = (some (.returned value),post)) :
    offsetNat input start 0 = 12 ∧ 12 ≤ offsetNat input start 1 ∧
      offsetNat input start 1 ≤ offsetNat input start 2 ∧ offsetNat input start 2 ≤ total ∧
      Decoded post input pointer array si start (offsetNat input start 0) (offsetNat input start 1) (offsetNat input start 2) total value ∧
      source.clock - post.clock ≤ 6 * (input.length % 2^64) + 17 ∧ post.clock ≤ source.clock := by
  let padding := 6 * (input.length % 2^64) + 28
  have paddedRun := panPropsEvaluateAddClockEq offsetBody source (some (.returned value)) post padding ⟨run,by intro impossible; cases impossible⟩
  have paddedEnvironment : Environment {source with clock := source.clock + padding}  := ⟨environment.domain,environment.allocCode,environment.failCode,environment.exceptionShape,environment.varCode,environment.code⟩
  obtain ⟨first,middleLower,ordered,lastUpper,loadedSource,innerPost,paid,paidBound,readyClock,control,arrays,endpoint,memory,globals,clock⟩ :=
    body_normal {source with clock := source.clock + padding} {post with clock := post.clock + padding} input pointer offsetArray array si start total
      paddedEnvironment heap minimum inside wp wlen offsets pointerLower pointerAligned offsetAligned offsetLower offsetBefore
      arrayAligned arrayAfter room heapGlobal offsetCode siLocal siArena siAligned siAfter siBefore
      (by change padding ≤ source.clock + padding; omega) value paddedRun
  have decoded := decoded_of_arrays _ _ input pointer array si start (offsetNat input start 0) (offsetNat input start 1) (offsetNat input start 2) total value arrays
  have lower := arrays
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,clockLower,clockUpper⟩ := lower
  change (loadedState loadedSource input start).clock - (6 * (input.length % 2^64) + 9) ≤ innerPost.clock at clockLower
  rw [readyClock] at clockLower
  change post.clock + padding = innerPost.clock at clock
  rw [← clock] at clockLower
  have forward := evaluateHOLFiniteState_clock_le source offsetBody
  rw [run] at forward
  change post.clock ≤ source.clock at forward
  have actualDecoded : Decoded post input pointer array si start (offsetNat input start 0) (offsetNat input start 1) (offsetNat input start 2) total value := by
    obtain ⟨codeArray,headerArray,finalCursor,returned,nodes,codes,headers,nodeSizes,codeSizes,headerCount,bytes,nodePointer,nodeCount,codePointer,codeCount,headerPointer,headerCountCell,heapCursor,codeAddress,headerAddress,codeAligned,headerAligned,finalAddress,finalBound,finalAligned⟩ := decoded
    have actualBytes := Blob.HeapInput.of_fields innerPost post input pointer memory.symm (by have h := congrArg PanSemStateFiniteExact.memaddrs endpoint; exact h.symm) (by have h := congrArg PanSemStateFiniteExact.be endpoint; exact h.symm) bytes
    exact ⟨codeArray,headerArray,finalCursor,returned,
      VarList.Records.of_memory innerPost post _ _ _ _ _ memory nodes,
      VarList.Records.of_memory innerPost post _ _ _ _ _ memory codes,
      VarList.Records.of_memory innerPost post _ _ _ _ _ memory headers,
      nodeSizes,codeSizes,headerCount,actualBytes,
      by rw [memory]; exact nodePointer,by rw [memory]; exact nodeCount,
      by rw [memory]; exact codePointer,by rw [memory]; exact codeCount,
      by rw [memory]; exact headerPointer,by rw [memory]; exact headerCountCell,
      by rw [globals]; exact heapCursor,codeAddress,headerAddress,codeAligned,headerAligned,finalAddress,finalBound,finalAligned⟩
  exact ⟨first,middleLower,ordered,lastUpper,actualDecoded,by dsimp only [padding] at clockLower; omega,forward⟩

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.decoded_of_arrays
#print axioms InitECandidate.Solver.Input.Witness.body_normal_any_clock
