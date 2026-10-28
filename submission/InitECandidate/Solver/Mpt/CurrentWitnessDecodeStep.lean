import InitECandidate.Solver.Mpt.CurrentWitnessDecodeSlices
import InitECandidate.Solver.Mpt.CurrentWitnessStepPrefixNormal
import InitECandidate.Solver.Mpt.WitnessDecodeStringTrace

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessStep
open Flapjack.Basis.Pure.MlString QueryBranch

theorem complete_payload_before (pointer length header payload heap : BitVec 64)
    (total : header.toNat+payload.toNat=length.toNat)
    (before : pointer.toNat+length.toNat≤heap.toNat) :
    payload.toNat≤length.toNat ∧ (pointer+header).toNat+payload.toNat≤heap.toNat := by
  have fits : pointer.toNat+header.toNat<2^64 := by have h:=heap.isLt; omega
  rw [BitVec.toNat_add_of_lt fits]
  omega

theorem current_suffix_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap : BitVec 64) (answer : ValueHOL 64)
    (complete : Rlp.Decode.Complete pointer length answer)
    (itemCell : source.locals.lookup (ofString "it")=some answer)
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source (afterRlp .decode)).2.clock≤length.toNat/4+149*length.toNat+270 := by
  obtain ⟨header,payload,flag,valueEq,headerBound,positive,total,binary,listHeader⟩:=complete
  rw [valueEq] at itemCell
  obtain ⟨payloadBound,payloadBefore⟩:=complete_payload_before pointer length header payload heap total before
  rcases slices_trace source _ pointer header payload flag itemCell binary arena.code _ rfl with stopped|entered
  · exact Nat.le_trans stopped (by omega)
  · obtain ⟨listFlag,run⟩:=entered
    have price:=current_slices_price source pointer header payload flag heap itemCell (by omega) payloadBefore heapCell heapArena heapBound aligned arena
    rw [run] at price
    have division : payload.toNat/4≤length.toNat/4:=Nat.div_le_div_right payloadBound
    exact Nat.le_trans price (by omega)

theorem current_suffix_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap : BitVec 64) (answer : ValueHOL 64)
    (complete : Rlp.Decode.Complete pointer length answer)
    (itemCell : source.locals.lookup (ofString "it")=some answer)
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) : ReturnFacts.Returns source (afterRlp .decode) ZeroResult := by
  intro post value normal
  obtain ⟨header,payload,flag,valueEq,headerBound,positive,total,binary,listHeader⟩:=complete
  rw [valueEq] at itemCell
  have guardRun:=string_guard_execute source pointer header payload flag itemCell
  by_cases zero : flag=0#64
  · have stops : (evaluateHOLFiniteState source stringGuard).1≠none := by
      rw [guardRun,if_pos zero]
      exact string_body_no_pass source arena.code
    rw [suffix_shape,sequence_stopped source stringGuard slicesCall stops,guardRun,if_pos zero] at normal
    obtain ⟨empty,valueEq,endpoint⟩:=string_body_normal source post pointer header payload flag itemCell value normal
    exact ⟨.val (.word 0#64),valueEq⟩
  · rw [if_neg zero] at guardRun
    rw [suffix_shape,evaluateHOLFiniteState_seq_line780,guardRun] at normal
    obtain ⟨payloadBound,payloadBefore⟩:=complete_payload_before pointer length header payload heap total before
    exact current_slices_zero source pointer header payload flag heap itemCell (by omega) payloadBefore heapCell heapArena heapBound aligned arena post value normal

/-- Complete all-outcome source-clock bound for the unchanged current
decode step, derived through its actual caught parser and slice conversion. -/
theorem current_step_price (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) :
    source.clock-(evaluateHOLFiniteState source (body .decode)).2.clock≤length.toNat/4+195*length.toNat+284 := by
  have fits : pointer.toNat+length.toNat<2^64:=by have h:=heap.isLt; omega
  rcases CurrentWitnessStep.parsed_suffix_trace .decode source _ db pointer length dbCell pointerCell lengthCell arena fits _ rfl with stopped|entered
  · exact Nat.le_trans stopped (by omega)
  · obtain ⟨ready,inner,answer,parsed,readyArena,frame,itemCell,currentDb,currentPointer,currentLength,forward,prefixPrice,continued,endpoint⟩:=entered
    have globals:=congrArg PanSemStateFiniteExact.globals frame
    change ready.globals=source.globals at globals
    have currentHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
    have suffix:=current_suffix_price ready pointer length heap answer parsed itemCell small before currentHeap heapArena heapBound aligned readyArena
    rw [continued] at suffix
    change ready.clock-inner.clock≤length.toNat/4+149*length.toNat+270 at suffix
    change (evaluateHOLFiniteState source (body .decode)).2=restore source "it" (restore (CurrentWitnessStep.tupleEntry source) "e" inner) at endpoint
    have endClock : (evaluateHOLFiniteState source (body .decode)).2.clock=inner.clock:=by rw [endpoint]; rfl
    rw [endClock]
    omega

/-- Every genuine normal decode result has flag zero. The extension and
branch scratch-frame paths cannot supply recursive work at main's arena. -/
theorem current_step_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) : ReturnFacts.Returns source (body .decode) ZeroResult := by
  intro post value normal
  have fits : pointer.toNat+length.toNat<2^64:=by have h:=heap.isLt; omega
  obtain ⟨ready,inner,answer,parsed,readyArena,frame,itemCell,currentDb,currentPointer,currentLength,forward,prefixPrice,continued,endpoint⟩:=
    CurrentWitnessStep.parsed_suffix_normal .decode source post db pointer length dbCell pointerCell lengthCell arena fits value normal
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change ready.globals=source.globals at globals
  have currentHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
  exact current_suffix_zero ready pointer length heap answer parsed itemCell small before currentHeap heapArena heapBound aligned readyArena inner value continued

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_suffix_price
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_suffix_zero
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_step_price
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_step_zero
