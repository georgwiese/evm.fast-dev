import InitECandidate.Solver.Mpt.CurrentWitnessDecodeListFrame
import InitECandidate.Solver.Mpt.CurrentWitnessDecodeStep

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessStep
open Flapjack.Basis.Pure.MlString QueryBranch

theorem current_suffix_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap : BitVec 64) (answer : ValueHOL 64)
    (complete : Rlp.Decode.Complete pointer length answer)
    (itemCell : source.locals.lookup (ofString "it")=some answer)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (afterRlp .decode)=(some (.returned value),post)) :
    TerminalResult heap value ∧ PersistentNormalFrame source post heap := by
  obtain ⟨header,payload,flag,valueEq,headerBound,positive,total,binary,listHeader⟩:=complete
  rw [valueEq] at itemCell
  have guardRun:=string_guard_execute source pointer header payload flag itemCell
  by_cases zero : flag=0#64
  · have stops : (evaluateHOLFiniteState source stringGuard).1≠none := by
      rw [guardRun,if_pos zero]
      exact string_body_no_pass source arena.code
    rw [suffix_shape,sequence_stopped source stringGuard slicesCall stops,guardRun,if_pos zero] at normal
    obtain ⟨empty,valueEq,endpoint⟩:=string_body_normal source post pointer header payload flag itemCell value normal
    rw [valueEq]
    exact ⟨TerminalResult.empty heap,(PersistentNormalFrame.refl source heap heapCell heapArena heapBound aligned).of_erase source source source post heap rfl (by rw [endpoint]; rfl)⟩
  · rw [if_neg zero] at guardRun
    rw [suffix_shape,evaluateHOLFiniteState_seq_line780,guardRun] at normal
    obtain ⟨payloadBound,payloadBefore⟩:=complete_payload_before pointer length header payload heap total before
    exact current_slices_frame source post pointer header payload flag heap pointer length itemCell pointerCell lengthCell
      (by omega) payloadBefore heapCell heapArena heapBound aligned arena value normal

/-- Complete actual current235 normal-return contract: a zero/fresh
terminal node, genuinely advanced bounded heap, unchanged earlier input,
unchanged nonheap globals and complete nonmemory runtime state. -/
theorem current_step_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (body .decode)=(some (.returned value),post)) :
    TerminalResult heap value ∧ PersistentNormalFrame source post heap := by
  have fits : pointer.toNat+length.toNat<2^64:=by have h:=heap.isLt; omega
  obtain ⟨ready,inner,answer,parsed,readyArena,pure,itemCell,currentDb,currentPointer,currentLength,forward,prefixPrice,continued,endpoint⟩:=
    CurrentWitnessStep.parsed_suffix_normal .decode source post db pointer length dbCell pointerCell lengthCell arena fits value normal
  have globals:=congrArg PanSemStateFiniteExact.globals pure
  change ready.globals=source.globals at globals
  have currentHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
  obtain ⟨nodeResult,frame⟩:=current_suffix_frame ready inner pointer length heap answer parsed itemCell currentPointer currentLength
    small before currentHeap heapArena heapBound aligned readyArena value continued
  exact ⟨nodeResult,frame.of_erase ready inner source post heap pure.symm (by rw [endpoint]; rfl)⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_suffix_frame
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_step_frame
