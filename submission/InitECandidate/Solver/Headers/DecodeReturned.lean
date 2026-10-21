import InitECandidate.Solver.Headers.DecodeEntryReturned
import InitECandidate.Solver.Headers.DecodeInitialState
import InitECandidate.Solver.Headers.PipelineMemory

namespace InitECandidate.Solver.Headers.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Actual normal whole-header output: real returned allocation, current
scratch/heap and preservation of all preceding ordinary decoded memory.
No output pointer, successful helper or later-state frame is supplied. -/
theorem body_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit : BitVec 64) (cutoff : Nat)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (inputLower : 2701131776≤pointer.toNat) (heapAligned : heap.toNat%8=0)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ output,value=.val (.word output) ∧ AllocatedBytes.Arena output 248 ∧ output.toNat%8=0 ∧ heap.toNat≤output.toNat ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded output 248#64))) ∧
      Rlp.Validation.Arena post cursor limit ∧ Input.HashInput.Frame source post cutoff heap.toNat ∧
      (∀ key,key≠ofString "heap_ptr" → post.globals.lookup key=source.globals.lookup key) ∧
      (PersistentAlloc.rounded output 248#64).toNat≤heap.toNat+616 := by
  obtain ⟨parsed,header,payload,sliced,items,count,final,topReturned,slicesReturned,countValid,funded,headerRoom,entryForward,entryPrice,continued,postEq⟩ :=
    field_entry_returned source post pointer length heap cursor limit cutoff pointerCell lengthCell arena heapGlobal heapBound before sizeBound aligned scratchBelow inputAbove installed value normal
  have state:=initial_field_state source parsed sliced pointer length header payload heap cursor limit count items cutoff topReturned slicesReturned countValid headerRoom installed inputLower heapAligned before aligned scratchBelow inputAbove
  let entry:=fieldEntry source parsed sliced pointer header payload heap count
  let current:=if count=23#64 then 1#64 else 0#64
  let output:=PersistentAlloc.rounded heap (count*16#64)
  have valid:=Pipeline.fields_valid current items.length state.branch
  rw [Pipeline.original_fields] at continued
  obtain ⟨valueEq,finish,active,finalState,erased⟩ := Pipeline.returned_state entry final (pointer+header) heap output cursor limit current payload.toNat cutoff items [] Pipeline.fields state valid value continued
  have postErased : Input.LocalEffects.erase post=Input.LocalEffects.erase finish := by rw [postEq]; exact erased
  have domain:=congrArg PanSemStateFiniteExact.memaddrs postErased
  have globals:=congrArg PanSemStateFiniteExact.globals postErased
  change post.memaddrs=finish.memaddrs at domain
  change post.globals=finish.globals at globals
  have outputAfter : heap.toNat≤output.toNat := by
    have h:=state.recordsBeforeHeader
    change heap.toNat+16*items.length≤output.toNat at h
    omega
  refine ⟨output,valueEq,finalState.headerArena,finalState.headerAligned,outputAfter,?_,?_,?_,?_,?_⟩
  · rw [globals]
    exact finalState.heap
  · exact Rlp.Validation.Arena.of_fields finish post cursor limit finalState.slices.arena domain globals
  · have frame:=Pipeline.memory_frame entry final (pointer+header) heap output cursor limit current payload.toNat cutoff items [] Pipeline.fields state valid (some (.returned value)) (Or.inr ⟨value,rfl⟩) continued
    obtain ⟨_,_,_,_,_,entryMemory,_⟩ := allocation_fields (listState source parsed sliced pointer header payload heap count) heap count output
    change entry.memory=sliced.memory at entryMemory
    refine ⟨?_⟩
    intro query lower upper
    have fieldWord:=frame query lower (upper.trans_le outputAfter)
    have prefixWord:=prefix_memory source parsed sliced pointer length header payload heap cursor limit count items topReturned slicesReturned query (scratchBelow.trans lower) (Or.inl upper)
    have memoryEq : post.memory=final.memory := by rw [postEq]; rfl
    rw [memoryEq,fieldWord,entryMemory]
    exact prefixWord
  · have pipelineGlobals:=Pipeline.globals_frame entry final (pointer+header) heap output cursor limit current payload.toNat cutoff items [] Pipeline.fields state valid (some (.returned value)) (Or.inr ⟨value,rfl⟩) continued
    intro key notHeap
    have finalGlobals : post.globals=final.globals := by rw [postEq]; rfl
    rw [finalGlobals,pipelineGlobals key]
    let listSource:=listState source parsed sliced pointer header payload heap count
    have currentGlobals:=congrArg PanSemStateFiniteExact.globals (counted_frame listSource heap count).1
    change (counted (declared listSource heap count) count).globals=listSource.globals at currentGlobals
    have entryGlobals : entry.globals.lookup key=sliced.globals.lookup key := by
      change ((counted (declared listSource heap count) count).globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded output 248#64)))).lookup key=_
      simp [HolFiniteMapExact.lookup_update,FUPDATE,notHeap,Ne.symm notHeap,currentGlobals]
      rfl
    rw [entryGlobals]
    exact prefix_globals source parsed sliced pointer length header payload heap cursor limit count items topReturned slicesReturned key notHeap

  · have firstSize : (count*16#64).toNat≤368 := by rcases countValid with rfl|rfl <;> decide
    have firstNumber:=PersistentAlloc.rounded_nat heap (count*16#64) (by omega)
    have outputBound : output.toNat≤heap.toNat+368 := by
      change (PersistentAlloc.rounded heap (count*16#64)).toNat≤_
      rw [firstNumber]
      omega
    have finalNumber:=PersistentAlloc.rounded_nat output 248#64 (by have h:=finalState.headerArena.upper; change output.toNat+248+7<2^64; omega)
    have aligned:=finalState.headerAligned
    rw [finalNumber]
    change (output.toNat+248+7)/8*8≤heap.toNat+616
    omega

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.body_returned
