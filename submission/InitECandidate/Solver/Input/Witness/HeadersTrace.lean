import InitECandidate.Solver.Input.Witness.Environment
import InitECandidate.Solver.Input.AllocationContext
import InitECandidate.Solver.Input.Witness.StoredListTrace

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- Actual final witness header-list call, SI stores and SI return, including
all parser/size exits and arbitrary real runtime funding. -/
theorem headers_trace_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
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
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source headerCall=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤2*((total-last)/4)+4 ∧
      ((∃ error : BitVec 64,(error=20#64 ∨ error=21#64 ∨ error=22#64 ∨ error=23#64 ∨ error=70#64) ∧ result=some (.exception (ofString "SszErr") (.val (.word error)))) ∨ (result=some (.returned (.val (.word si))) ∧
        (∀ query,query.toNat<array.toNat → query≠byteAddress si 72 → query≠byteAddress si 80 → post.memory query=source.memory query) ∧ InitializerAllocations.context post=InitializerAllocations.context source)) := by
  classical
  have args := list_arguments source pointer start last total 256 1024 "w2" "wlen" ordered
    (by have := Nat.mod_lt input.length (by decide : 0<2^64); omega) wp lastLocal totalLocal
  rw [arrays_shape.2.2.2.2.1,arrays_shape.2.2.2.2.2] at run
  rcases stored_list_trace source post input pointer array 256#64 1024#64 si (start+last) (total-last) 72 heap (by omega)
    environment.domain lower aligned arrayAligned arrayAfter room heapGlobal environment.allocCode environment.failCode environment.exceptionShape environment.varCode environment.code
    siLocal siArena siAligned siAfter siBefore (by decide) (by decide) "hd" (by decide) (listArguments "w2" "wlen" 256 1024) returnInput args result run notTimeout with rejected | normal
  · obtain ⟨error,allowed,same,cost⟩ := rejected
    exact ⟨cost,Or.inl ⟨error,allowed,same⟩⟩
  · obtain ⟨next,innerPost,locals,records,countLimit,sizes,nextHeap,firstCell,secondCell,nextCursor,cost,forward,frame,control,returnRun,endpoint⟩ := normal
    have nextSi := local_after_tuple source next "hd" "si" _ _ (by decide) locals siLocal
    have returned : evaluateHOLFiniteState next returnInput=(some (.returned (.val (.word si))),emptyLocalsHOLFinite next) := by
      simp [returnInput,evaluateHOLFiniteState_return,localVar,evalHOLExact,toExact,nextSi,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    have equality := returned.symm.trans returnRun
    have same := congrArg Prod.fst equality
    have clocks := congrArg (fun output => output.2.clock) equality
    have clock : post.clock=next.clock := by rw [endpoint]; exact clocks.symm
    have innerEq : innerPost=emptyLocalsHOLFinite next := (congrArg Prod.snd equality).symm
    have memory : post.memory=next.memory := by rw [endpoint,innerEq]; rfl
    have readonly : InitializerAllocations.context post=InitializerAllocations.context source := by
      rw [endpoint,innerEq]
      exact allocation_context source next array _ (total-last=0) control
    exact ⟨by rw [clock]; exact cost,Or.inr ⟨same.symm,(by
      intro query before firstAway secondAway
      rw [memory]
      exact frame query before firstAway secondAway),readonly⟩⟩


/-- The bound/outcome projection of the stronger actual-memory contract. -/
theorem headers_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
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
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source headerCall=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤2*((total-last)/4)+4 ∧
      ((∃ error : BitVec 64,(error=20#64 ∨ error=21#64 ∨ error=22#64 ∨ error=23#64 ∨ error=70#64) ∧ result=some (.exception (ofString "SszErr") (.val (.word error)))) ∨ result=some (.returned (.val (.word si)))) := by
  obtain ⟨cost,outcome⟩ := headers_trace_frame source post input pointer array si start last total environment heap ordered inside lower aligned arrayAligned arrayAfter room heapGlobal wp lastLocal totalLocal siLocal siArena siAligned siAfter siBefore result run notTimeout
  exact ⟨cost,outcome.imp id (fun normal => normal.1)⟩

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.headers_trace

#print axioms InitECandidate.Solver.Input.Witness.headers_trace_frame
