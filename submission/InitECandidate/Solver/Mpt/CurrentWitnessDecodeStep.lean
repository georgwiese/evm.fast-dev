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
    source.clock-(evaluateHOLFiniteState source (afterRlp .decode)).2.clock≤length.toNat/4+191*length.toNat+270 := by
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

private theorem string_body_binary (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    ReturnFacts.Returns source stringBody BinaryResult := by
  apply ReturnFacts.sequence
  · exact ReturnFacts.conditional source _ _ _ BinaryResult
      (binary_pair_return source 0#64 (.const 0#64) (Or.inl rfl)) (ReturnFacts.skip source BinaryResult)
  · intro middle normal post value actual
    exact (NoReturn.ignored_call (ofString "mpt_fail") [.const 4#64] middle value (congrArg Prod.fst actual)).elim

/-- Both real suffix outcomes have their syntactic terminal/suspended tag;
no old scratch-store failure is used to eliminate pending work. -/
theorem current_suffix_binary (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    ReturnFacts.Returns source (afterRlp .decode) BinaryResult := by
  rw [suffix_shape]
  apply ReturnFacts.sequence
  · exact ReturnFacts.conditional source _ _ _ BinaryResult (string_body_binary source) (ReturnFacts.skip source BinaryResult)
  · intro middle normal
    exact current_slices_binary middle

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
    source.clock-(evaluateHOLFiniteState source (body .decode)).2.clock≤length.toNat/4+251*length.toNat+284 := by
  have fits : pointer.toNat+length.toNat<2^64:=by have h:=heap.isLt; omega
  rcases CurrentWitnessStep.parsed_suffix_trace .decode source _ db pointer length dbCell pointerCell lengthCell arena fits _ rfl with stopped|entered
  · exact Nat.le_trans stopped (by omega)
  · obtain ⟨ready,inner,answer,parsed,readyArena,frame,itemCell,currentDb,currentPointer,currentLength,forward,prefixPrice,continued,endpoint⟩:=entered
    have globals:=congrArg PanSemStateFiniteExact.globals frame.metadata
    change ready.globals=source.globals at globals
    have currentHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [globals]; exact heapCell
    have suffix:=current_suffix_price ready pointer length heap answer parsed itemCell small before currentHeap heapArena heapBound aligned readyArena
    rw [continued] at suffix
    change ready.clock-inner.clock≤length.toNat/4+191*length.toNat+270 at suffix
    change (evaluateHOLFiniteState source (body .decode)).2=restore source "it" (restore (CurrentWitnessStep.tupleEntry source) "e" inner) at endpoint
    have endClock : (evaluateHOLFiniteState source (body .decode)).2.clock=inner.clock:=by rw [endpoint]; rfl
    rw [endClock]
    omega

/-- Every real normal decode step returns a finished node or a pending
frame. This is a structural consequence of the unchanged actual body. -/
theorem current_step_binary (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    ReturnFacts.Returns source (body .decode) BinaryResult := by
  rw [body_shape]
  apply ReturnFacts.declared
  intro tuple
  apply ReturnFacts.declared
  intro error
  apply ReturnFacts.sequence
  · have never : NoReturn.Never (caught .decode):=
      NoReturn.caught_destination (some (.local,ofString "it")) (ofString (rlpName .decode)) arguments
        (ofString "RlpErr") (ofString "e") handler (NoReturn.ignored_call (ofString "mpt_fail") [.const 3#64])
    intro post value normal
    exact (never _ value (congrArg Prod.fst normal)).elim
  · intro middle normal
    exact current_suffix_binary middle

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_suffix_price
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_suffix_binary
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_step_price
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_step_binary
