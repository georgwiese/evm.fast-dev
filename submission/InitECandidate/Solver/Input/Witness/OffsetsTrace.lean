import InitECandidate.Solver.Input.Witness.LoopTrace
import InitECandidate.Solver.Input.OffsetsTrace

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

theorem offset_tail_shape : offsetTail = .seq offsetGuard loadedBody := offset_shapes.2.2.1

/-- Actual witness offsets on all non-timeout outcomes: the three real scratch
writes and validator either raise SszErr10/11/12 within8 source ticks or
reach the original witness byte-list declarations with validated offsets and bytes. -/
theorem offsets_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array total : BitVec 64) (start : Nat)
    (heap : Blob.HeapInput source input pointer) (extent : start + 12 ≤ input.length % 2^64)
    (wp : source.locals.lookup (ofString "wp") = some (.val (.word (pointer + BitVec.ofNat 64 start))))
    (n : source.locals.lookup (ofString "wlen") = some (.val (.word total)))
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word array)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (pointerAligned : pointer.toNat % 8 = 0)
    (arrayAligned : array.toNat % 8 = 0) (arrayLower : 2701131776 ≤ array.toNat)
    (before : array.toNat + 24 ≤ pointer.toNat) (upper : pointer.toNat + input.length % 2^64 + 8 ≤ 33806089496)
    (code : source.code.lookup (ofString "ssz_check_offsets") = some (Offsets.formals,Offsets.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail") = some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source offsetBody = (result,post)) (notTimeout : result ≠ some .timeOut) :
    (∃ error : BitVec 64,(error = 10#64 ∨ error = 11#64 ∨ error = 12#64) ∧ result = some (.exception (ofString "SszErr") (.val (.word error))) ∧ source.clock - post.clock ≤ 8) ∨
    (offsetWord input start 0 = 12#64 ∧ (∀ position < 3,Offsets.ValidAt 12#64 total (offsetWord input start) position) ∧
      ∃ next innerPost,next.clock ≤ source.clock ∧ source.clock - next.clock ≤ 8 ∧ BackingLayout.control next = BackingLayout.control source ∧
        Blob.HeapInput next input pointer ∧ (∀ name,name ≠ ofString "i" → next.locals.lookup name = source.locals.lookup name) ∧
        (∀ position < 3,next.memory (byteAddress array (8*position)) = .word (offsetWord input start position)) ∧
        evaluateHOLFiniteState next loadedBody = (result,innerPost) ∧ post = restore source "i" innerPost ∧
        (∀ query,query.toNat < array.toNat ∨ array.toNat + 24 ≤ query.toNat → next.memory query = source.memory query)) := by
  obtain ⟨funded,loopTarget,innerPost,loopClock,control,loopHeap,other,cells,remaining,restored,loopMemory⟩ := loop_trace source post input pointer array start heap extent wp offsets domain pointerAligned arrayAligned arrayLower before upper result run notTimeout
  have globals : loopTarget.globals = source.globals := by have h := congrArg PanSemStateFiniteExact.globals control; exact h
  have codes : loopTarget.code = source.code := by have h := congrArg PanSemStateFiniteExact.code control; exact h
  have shapes : loopTarget.eshapes = source.eshapes := by have h := congrArg PanSemStateFiniteExact.eshapes control; exact h
  have domains : loopTarget.memaddrs = source.memaddrs := by have h := congrArg PanSemStateFiniteExact.memaddrs control; exact h
  have localLength := (other (ofString "wlen") (by decide)).trans n
  have loopOffsets : loopTarget.globals.lookup (ofString "ssz_offs") = some (.val (.word array)) := by rw [globals]; exact offsets
  have args : evalListHOLFinite loopTarget (h := fun address => Classical.propDecidable (loopTarget.memaddrs address)) offsetArguments = some (Offsets.arguments array 12#64 total 3) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,offsetArguments,Offsets.arguments,Header.offsets,localVar,loopOffsets,localLength]
  have mapped (position : Nat) (small : position < 3) : loopTarget.memaddrs (array + BitVec.ofNat 64 (8*position)) :=
    word_mapped loopTarget array 24 (8*position) (domains.trans domain) ⟨arrayLower,by omega⟩ (by omega) arrayAligned (by omega)
  rw [offset_tail_shape,offsetGuard] at remaining
  obtain ⟨target,paid,bound,enough,targetClock,outcome⟩ := Offsets.call_trace loopTarget innerPost offsetArguments loadedBody array 12#64 total (offsetWord input start) 3
    (by decide) (by decide) args (by rw [codes]; exact code) (by rw [codes]; exact failCode) (by rw [shapes]; exact exceptionShape) mapped cells result remaining notTimeout
  rcases outcome with normal | fault
  · obtain ⟨called,targetEq,first,valid,targetRun⟩ := normal
    have targetHeap : Blob.HeapInput target input pointer := by rw [targetEq]; exact loopHeap
    have targetControl : BackingLayout.control target = BackingLayout.control source := by rw [targetEq]; exact control
    have targetLocals (name : MlS) (different : name ≠ ofString "i") : target.locals.lookup name = source.locals.lookup name := by rw [targetEq]; exact other name different
    have targetCells (position : Nat) (small : position < 3) : target.memory (byteAddress array (8*position)) = .word (offsetWord input start position) := by rw [targetEq]; exact cells position small
    exact Or.inr ⟨first,valid,target,innerPost,by omega,by omega,targetControl,targetHeap,targetLocals,targetCells,targetRun,restored,by intro query outside; rw [targetEq]; exact loopMemory query outside⟩
  · obtain ⟨error,allowed,called,same,endpoint⟩ := fault
    have postClock : post.clock = target.clock := by rw [restored,endpoint]; rfl
    exact Or.inl ⟨error,allowed,same,by rw [postClock]; omega⟩

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.offset_tail_shape
#print axioms InitECandidate.Solver.Input.Witness.offsets_trace
