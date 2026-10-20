import InitECandidate.Solver.Input.Witness.ArraysTrace
import InitECandidate.Solver.Input.Witness.OffsetsTrace
import InitECandidate.Solver.Input.Witness.OffsetValues
import InitECandidate.Solver.Input.Witness.LoadedOffsets
import InitECandidate.Solver.Input.Witness.ControlFields

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000

/-- Entire original witness offset/list body on every non-timeout outcome.
The shared encoded slice gives total/2+20 source ticks, including every
malformed offset/header/record/count/size exit and all actual SI stores. -/
theorem body_trace_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
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
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source offsetBody=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤total/2+20 ∧
      ((∃ error : BitVec 64,(error=10#64 ∨ error=11#64 ∨ error=12#64 ∨ error=20#64 ∨ error=21#64 ∨ error=22#64 ∨ error=23#64 ∨ error=70#64) ∧ result=some (.exception (ofString "SszErr") (.val (.word error)))) ∨ (result=some (.returned (.val (.word si))) ∧
        (∀ query,query.toNat<array.toNat → (query.toNat<offsetArray.toNat ∨ offsetArray.toNat+24≤query.toNat) →
          query≠byteAddress si 40 → query≠byteAddress si 48 → query≠byteAddress si 56 → query≠byteAddress si 64 → query≠byteAddress si 72 → query≠byteAddress si 80 → post.memory query=source.memory query) ∧ InitializerAllocations.context post=InitializerAllocations.context source)) := by
  have prefixExtent : start+12≤input.length%2^64 := by omega
  have upper : pointer.toNat+input.length%2^64+8≤33806089496 := by omega
  rcases offsets_trace source post input pointer offsetArray (BitVec.ofNat 64 total) start heap prefixExtent wp wlen offsets environment.domain pointerAligned offsetAligned offsetLower offsetBefore upper
    offsetCode environment.failCode environment.exceptionShape result run notTimeout with rejected | normal
  · obtain ⟨error,allowed,same,cost⟩ := rejected
    exact ⟨by omega,Or.inl ⟨error,by rcases allowed with rfl | rfl | rfl <;> simp,same⟩⟩
  obtain ⟨first,valid,next,innerPost,nextForward,nextCost,control,nextBytes,other,cells,remaining,endpoint,memory⟩ := normal
  have totalNumber : (BitVec.ofNat 64 total).toNat=total := by
    have small := Nat.mod_lt input.length (show 0<2^64 by decide)
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨firstNat,middleLower,ordered,lastUpper⟩ := offset_values input start (BitVec.ofNat 64 total) first valid
  rw [totalNumber] at lastUpper
  have nextOffsets := global_of_control source next (ofString "ssz_offs") (.val (.word offsetArray)) control offsets
  have nextEnvironment := Environment.of_control source next control environment
  have mapped (position : Nat) (small : position<3) : next.memaddrs (byteAddress offsetArray (8*position)) :=
    word_mapped next offsetArray 24 (8*position) nextEnvironment.domain ⟨offsetLower,by omega⟩ (by omega) offsetAligned (by omega)
  rw [loaded_offsets_execute next input offsetArray start nextOffsets mapped cells] at remaining
  let ready := loadedState next input start
  let final := (evaluateHOLFiniteState ready nodeCall).2
  have observed := congrArg Prod.fst remaining
  have actual : evaluateHOLFiniteState ready nodeCall=(result,final) := Prod.ext observed rfl
  have restored : innerPost=restoreLoaded next input start final := (congrArg Prod.snd remaining).symm
  have readyControl : BackingLayout.control ready=BackingLayout.control source := control
  have readyEnvironment := Environment.of_control source ready readyControl environment
  have readyHeap := Blob.HeapInput.of_fields next ready input pointer rfl rfl rfl nextBytes
  have readyWp := (loaded_other_local next input start (ofString "wp") (by decide)).trans ((other _ (by decide)).trans wp)
  have readyWlen := (loaded_other_local next input start (ofString "wlen") (by decide)).trans ((other _ (by decide)).trans wlen)
  have readySi := (loaded_other_local next input start (ofString "si") (by decide)).trans ((other _ (by decide)).trans siLocal)
  have readyFields := loaded_offset_locals next input start
  have readyHeapGlobal := global_of_control source ready (ofString "heap_ptr") (.val (.word array)) readyControl heapGlobal
  obtain ⟨cost,outcome⟩ := arrays_trace_frame ready final input pointer array si start (offsetNat input start 0) (offsetNat input start 1) (offsetNat input start 2) total
    readyEnvironment readyHeap ⟨by omega,ordered,lastUpper⟩ inside pointerLower pointerAligned arrayAligned arrayAfter room readyHeapGlobal
    readyWp readyFields.1 readyFields.2.1 readyFields.2.2 readyWlen readySi siArena siAligned siAfter siBefore result actual notTimeout
  have clocks : post.clock=final.clock := by rw [endpoint,restored]; rfl
  have finalForward := evaluateHOLFiniteState_clock_le ready nodeCall
  rw [actual] at finalForward
  change final.clock≤next.clock at finalForward
  change next.clock-final.clock≤(total-offsetNat input start 0)/2+12 at cost
  refine ⟨by rw [clocks]; omega,?_⟩
  rcases outcome with rejected | normal
  · obtain ⟨error,allowed,same⟩ := rejected
    exact Or.inl ⟨error,Or.inr (Or.inr (Or.inr allowed)),same⟩
  · have postMemory : post.memory=final.memory := by rw [endpoint,restored]; rfl
    have readyContext : InitializerAllocations.context ready=InitializerAllocations.context source := by have h := congrArg InitializerAllocations.context readyControl; exact h
    have postContext : InitializerAllocations.context post=InitializerAllocations.context final := by rw [endpoint,restored]; rfl
    have readonly := postContext.trans (normal.2.2.trans readyContext)
    refine Or.inr ⟨normal.1,?_,readonly⟩
    intro query before outside nodePtr nodeCount codePtr codeCount headerPtr headerCount
    rw [postMemory]
    exact (normal.2.1 query before nodePtr nodeCount codePtr codeCount headerPtr headerCount).trans (memory query outside)



/-- Bound/outcome projection of the stronger original witness memory frame. -/
theorem body_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
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
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source offsetBody=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤total/2+20 ∧
      ((∃ error : BitVec 64,(error=10#64 ∨ error=11#64 ∨ error=12#64 ∨ error=20#64 ∨ error=21#64 ∨ error=22#64 ∨ error=23#64 ∨ error=70#64) ∧ result=some (.exception (ofString "SszErr") (.val (.word error)))) ∨ result=some (.returned (.val (.word si)))) := by
  obtain ⟨cost,outcome⟩ := body_trace_frame source post input pointer offsetArray array si start total environment heap minimum inside wp wlen offsets pointerLower pointerAligned offsetAligned offsetLower offsetBefore arrayAligned arrayAfter room heapGlobal offsetCode siLocal siArena siAligned siAfter siBefore result run notTimeout
  exact ⟨cost,outcome.imp id (fun normal => normal.1)⟩

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.body_trace

#print axioms InitECandidate.Solver.Input.Witness.body_trace_frame
