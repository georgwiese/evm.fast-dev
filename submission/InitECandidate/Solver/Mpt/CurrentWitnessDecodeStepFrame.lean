import InitECandidate.Solver.Mpt.CurrentWitnessDecodeListFrame
import InitECandidate.Solver.Mpt.CurrentWitnessDecodeStep

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessStep
open Flapjack.Basis.Pure.MlString QueryBranch

theorem current_suffix_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64) (answer : ValueHOL 64)
    (complete : Rlp.Decode.Complete pointer length answer)
    (itemCell : source.locals.lookup (ofString "it")=some answer)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) (physical : Rlp.Validation.Arena source cursor limit)
    (dbBefore : db.toNat≤heap.toNat) (lower : 2701131776≤pointer.toNat)
    (parentBefore : pointer.toNat+length.toNat≤db.toNat)
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (afterRlp .decode)=(some (.returned value),post)) :
    LiveFrame source post heap cursor limit ∧ NormalResult post db pointer length heap cursor limit value := by
  obtain ⟨header,payload,flag,valueEq,headerBound,positive,total,binary,listHeader⟩:=complete
  rw [valueEq] at itemCell
  have guardRun:=string_guard_execute source pointer header payload flag itemCell
  by_cases zero : flag=0#64
  · have stops : (evaluateHOLFiniteState source stringGuard).1≠none := by
      rw [guardRun,if_pos zero]
      exact string_body_no_pass source live.code
    rw [suffix_shape,sequence_stopped source stringGuard slicesCall stops,guardRun,if_pos zero] at normal
    obtain ⟨empty,valueEq,endpoint⟩:=string_body_normal source post pointer header payload flag itemCell value normal
    rw [valueEq]
    have selfFrame:=LiveFrame.of_persistent source source heap cursor limit live physical
      (PersistentNormalFrame.refl source heap heapCell heapArena heapBound aligned) (Rlp.Validation.Above.refl source cursor.toNat)
    exact ⟨LiveFrame.of_erase source source source post heap cursor limit selfFrame rfl (by rw [endpoint]; rfl),
      .empty (physical.of_fields source post cursor limit (by rw [endpoint]; rfl) (by rw [endpoint]; rfl))⟩
  · rw [if_neg zero] at guardRun
    rw [suffix_shape,evaluateHOLFiniteState_seq_line780,guardRun] at normal
    obtain ⟨payloadBound,payloadBefore⟩:=complete_payload_before pointer length header payload heap total before
    have pointerNumber : (pointer+header).toNat=pointer.toNat+header.toNat:=
      BitVec.toNat_add_of_lt (by have h:=heap.isLt; omega)
    exact current_slices_frame source post db pointer header payload flag heap pointer length cursor limit itemCell pointerCell lengthCell
      (by omega) payloadBefore heapCell heapArena heapBound aligned live physical dbBefore small lower parentBefore
      (by rw [pointerNumber]; omega) (by rw [pointerNumber]; omega) value normal

/-- The complete actual decoder returns its physical empty/leaf/pending
result. Its real parser and allocation stages protect earlier persistent
data and older live records; pending records carry actual allowance progress. -/
theorem current_step_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit : BitVec 64)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (small : length.toNat≤1024) (before : pointer.toNat+length.toNat≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) (physical : Rlp.Validation.Arena source cursor limit)
    (dbBefore : db.toNat≤heap.toNat) (lower : 2701131776≤pointer.toNat)
    (parentBefore : pointer.toNat+length.toNat≤db.toNat)
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (body .decode)=(some (.returned value),post)) :
    LiveFrame source post heap cursor limit ∧ NormalResult post db pointer length heap cursor limit value := by
  have fits : pointer.toNat+length.toNat<2^64:=by have h:=heap.isLt; omega
  obtain ⟨ready,inner,answer,parsed,readyLive,prefixFrame,above,itemCell,currentDb,currentPointer,currentLength,forward,prefixPrice,continued,endpoint⟩:=
    CurrentWitnessStep.parsed_suffix_normal .decode source post db pointer length dbCell pointerCell lengthCell live fits value normal
  have globals:=congrArg PanSemStateFiniteExact.globals prefixFrame.metadata
  change ready.globals=source.globals at globals
  have currentHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
  have domain:=MemoryMetadata.domain prefixFrame.metadata
  have readyPhysical:=physical.of_fields source ready cursor limit domain globals
  have beforeFrame : ∀ query : BitVec 64,query.toNat<heap.toNat → ready.memory query=source.memory query:=
    fun query earlier=>prefixFrame.outside query (Or.inl (by omega))
  have first:=LiveFrame.of_parser source ready heap cursor limit live physical heapCell heapArena heapBound aligned
    prefixFrame.metadata beforeFrame (above cursor limit physical)
  obtain ⟨tail,result⟩:=current_suffix_frame ready inner db pointer length heap cursor limit answer parsed itemCell currentPointer currentLength
    small before currentHeap heapArena heapBound aligned readyLive readyPhysical dbBefore lower parentBefore value continued
  have complete:=LiveFrame.compose source ready inner heap cursor heap cursor limit first tail (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨LiveFrame.of_erase source inner source post heap cursor limit complete rfl (by rw [endpoint]; rfl),
    result.of_fields inner post db pointer length heap cursor limit value (by rw [endpoint]; rfl)
      (by rw [endpoint]; rfl) (by rw [endpoint]; rfl)⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_suffix_frame
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_step_frame
