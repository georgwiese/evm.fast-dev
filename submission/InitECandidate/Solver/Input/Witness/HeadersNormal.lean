import InitECandidate.Solver.Input.Witness.Environment

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- Normal execution of the literal final header-list call stores its actual
array/count, enforces the 256-header cap and returns the same SI pointer. -/
theorem headers_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array si : BitVec 64) (start last total : Nat)
    (environment : Environment source) (heap : Blob.HeapInput source input pointer)
    (ordered : last≤total) (inside : start+total≤input.length%2^64)
    (lower : 2701131776≤pointer.toNat) (aligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (arrayAfter : pointer.toNat+input.length%2^64+8≤array.toNat)
    (room : array.toNat+4*(total-last)≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word array)))
    (wp : source.locals.lookup (ofString "wp")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (lastLocal : source.locals.lookup (ofString "w2")=some (.val (.word (BitVec.ofNat 64 last))))
    (totalLocal : source.locals.lookup (ofString "wlen")=some (.val (.word (BitVec.ofNat 64 total))))
    (siLocal : source.locals.lookup (ofString "si")=some (.val (.word si)))
    (siArena : Arena si 96) (siAligned : si.toNat%8=0) (siAfter : pointer.toNat+input.length%2^64+8≤si.toNat)
    (siBefore : si.toNat+96≤array.toNat)
    (enough : 2*((total-last)/4)+5≤source.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source headerCall=(some (.returned value),post)) :
    value=.val (.word si) ∧ VarList.Records post input pointer array (start+last) (total-last) ∧
      VarList.decodedCount input (start+last) (total-last)≤256 ∧
      (∀ index<VarList.decodedCount input (start+last) (total-last),
        (VarList.recordLength input (start+last) (total-last) (VarList.decodedCount input (start+last) (total-last)) index).toNat≤1024) ∧
      Blob.HeapInput post input pointer ∧ post.memory (byteAddress si 72)=.word (VarList.decodedArray array (total-last)) ∧
      post.memory (byteAddress si 80)=.word (BitVec.ofNat 64 (VarList.decodedCount input (start+last) (total-last))) ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (VarList.nextCursor array (VarList.decodedCount input (start+last) (total-last))))) ∧
      source.clock-(2*((total-last)/4)+3)≤post.clock ∧ post.clock≤source.clock ∧
      (∀ query,query.toNat<array.toNat → query≠byteAddress si 72 → query≠byteAddress si 80 → post.memory query=source.memory query) ∧
      BackingLayout.control post=BackingLayout.control
        (if total-last=0 then source else PersistentAlloc.post source array (BitVec.ofNat 64 (16*(Guest.GasLimit.le32 input (start+last)/4)))) := by
  classical
  have args:=list_arguments source pointer start last total 256 1024 "w2" "wlen" ordered
    (by have:=Nat.mod_lt input.length (by decide : 0<2^64);omega) wp lastLocal totalLocal
  rw [arrays_shape.2.2.2.2.1,arrays_shape.2.2.2.2.2] at run
  obtain ⟨next,innerPost,locals,records,countLimit,lengthBound,nextHeap,firstCell,secondCell,nextCursor,
      clockLower,clockUpper,frame,control,returnRun,postEq⟩:=stored_list_normal source post input pointer array 256#64 1024#64 si
    (start+last) (total-last) 72 heap (by omega) environment.domain lower aligned arrayAligned arrayAfter room heapGlobal
    environment.allocCode environment.failCode environment.exceptionShape environment.varCode environment.code
    siLocal siArena siAligned siAfter siBefore (by decide) (by decide) "hd" (by decide)
    (listArguments "w2" "wlen" 256 1024) returnInput args enough value run
  have nextSi:=local_after_tuple source next "hd" "si" _ _ (by decide) locals siLocal
  have returned : evaluateHOLFiniteState next returnInput=(some (.returned (.val (.word si))),emptyLocalsHOLFinite next) := by
    simp [returnInput,evaluateHOLFiniteState_return,localVar,evalHOLExact,toExact,nextSi,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have normal:=returned.symm.trans returnRun
  have valueEq : value=.val (.word si) := by
    have result:=congrArg Prod.fst normal
    cases result
    rfl
  have innerEq : innerPost=emptyLocalsHOLFinite next:=(congrArg Prod.snd normal).symm
  have memory : post.memory=next.memory := by rw [postEq,innerEq];rfl
  have domains : next.memaddrs=post.memaddrs := by rw [postEq,innerEq];rfl
  have endian : next.be=post.be := by rw [postEq,innerEq];rfl
  have globals : post.globals=next.globals := by rw [postEq,innerEq];rfl
  have clocks : post.clock=next.clock := by rw [postEq,innerEq];rfl
  have controls : BackingLayout.control post=BackingLayout.control next := by rw [postEq,innerEq];rfl
  refine ⟨valueEq,VarList.Records.of_memory next post input pointer array (start+last) (total-last) memory records,
    countLimit,lengthBound,Blob.HeapInput.of_fields next post input pointer memory.symm domains endian nextHeap,
    ?_,?_,?_,?_,?_,?_,controls.trans control⟩
  · rw [memory];exact firstCell
  · rw [memory];exact secondCell
  · rw [globals];exact nextCursor
  · rw [clocks];exact clockLower
  · rw [clocks];exact clockUpper
  · intro query before firstAway secondAway
    rw [memory]
    exact frame query before firstAway secondAway

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.headers_normal
