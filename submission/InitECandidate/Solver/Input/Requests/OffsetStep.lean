import InitECandidate.Solver.Input.Requests.Program
import InitECandidate.Solver.Input.LocalWord

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

def offsetNext (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (array : BitVec 64) (start index : Nat) : PanSemStateFiniteExact 64 Guest.HostMemory:=
  bind {source with memory:=StoreWord.put source.memory (byteAddress array (8*index)) (offsetWord input start index)}
    "i" (BitVec.ofNat 64 (index+1))

theorem offset_test (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat) (inside : index≤5)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source offsetTest=some (.val (.word (if index<5 then 1#64 else 0#64))) := by
  have number : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have sign : index<9223372036854775808:=by omega
  simp [eval,offsetTest,localVar,evalHOLExact,toExact,i,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,BitVec.lt_def,number,sign]

/-- A real offset-store loop body reads its four copied bytes, writes the
corresponding low scratch cell, and increments the actual loop index. -/
theorem offset_step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start index : Nat) (inside : index<5)
    (heap : Blob.HeapInput source input pointer) (extent : start+20≤input.length%2^64)
    (wp : source.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (offsets : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (pointerAligned : pointer.toNat%8=0)
    (arrayAligned : array.toNat%8=0) (arrayLower : 2701131776≤array.toNat)
    (before : array.toNat+40≤pointer.toNat) (upper : pointer.toNat+input.length%2^64+8≤33806089496) :
    evaluateHOLFiniteState source offsetStep=(none,offsetNext source input array start index) ∧
      Blob.HeapInput (offsetNext source input array start index) input pointer ∧
      (offsetNext source input array start index).memory (byteAddress array (8*index))=.word (offsetWord input start index) ∧
      (∀ query,query≠byteAddress array (8*index) → (offsetNext source input array start index).memory query=source.memory query) := by
  classical
  let stored : PanSemStateFiniteExact 64 Guest.HostMemory:=
    {source with memory:=StoreWord.put source.memory (byteAddress array (8*index)) (offsetWord input start index)}
  have arrayArena : Arena array 40:=⟨arrayLower,by omega⟩
  have address : eval source offsetAddress=some (.val (.word (byteAddress array (8*index)))) := by
    simp [eval,offsetAddress,Header.offsets,localVar,evalHOLExact,evalListHOLExact,toExact,offsets,i,
      valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,byteAddress,←BitVec.ofNat_mul,Nat.mul_comm]
  have read:=offset_input_read source input pointer start index heap (by omega) wp i
  have storeRun:=StoreWord.execute source offsetAddress offsetRead _ _ address read
    (word_mapped source array 40 (8*index) domain arrayArena (by omega) arrayAligned (by omega))
  have incrementRead : eval stored (.op .add [localVar "i",.const 1#64])=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
    simpa only [Scalar.plus,BitVec.ofNat_add] using Scalar.plus_read stored (localVar "i") (BitVec.ofNat 64 index) 1
      (Request.local_word stored "i" _ i)
  have assigned:=StateSteps.assign_execute stored "i" (.op .add [localVar "i",.const 1#64]) _ _ i incrementRead
  have number:=byteAddress_toNat array (8*index) (by omega)
  refine ⟨?_,?_,?_,?_⟩
  · exact (StateSteps.next_sequence source stored offsetStore offsetIncrement storeRun (Nat.le_refl _)).trans assigned
  · exact Blob.HeapInput.store_separate source input pointer _ _ heap pointerAligned (by omega) (Or.inl (by rw [number];omega))
  · simp [offsetNext,QueryBranch.bind,setVarHOLFinite,StoreWord.put]
  · intro query away
    simp [offsetNext,QueryBranch.bind,setVarHOLFinite,StoreWord.put,away]

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.offset_test
#print axioms InitECandidate.Solver.Input.Requests.offset_step
