import InitECandidate.Solver.Input.MainWitnessConstructorInputs
import InitECandidate.Solver.Input.RunAttemptHeaderPrefix

namespace InitECandidate.Solver.Input.Main.RunAttemptData
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem block_hash_names : ofString "block_hashes"∈OriginalScalarGlobals.names ∧ ofString "block_hashes_n"∈OriginalScalarGlobals.names := by decide_cbv

/-- The actual main hash continuation supplies the original run_attempt
validator arguments, payload read, scalar-global shapes and physical SI
allocation after its wrapper-only local/clock changes. -/
theorem entry_data (input : Guest.InputBlob)
    (before copiedSource origin hashed source : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts) (returned : RequestHash.Returned input origin hashed root)
    (entryFrame : LocalEffects.erase source=LocalEffects.erase hashed) :
    ∃ headerArray,Headers.Validate.Context source (VarList.decodedArray headerArray (HeaderSlices.bytes input)) (PersistentAlloc.rounded root 32#64)
        (BitVec.ofNat 64 (HeaderSlices.count input)) 2713714688#64 2701135872#64 2713714976#64 2713715176#64
        (HeaderSlices.pointer input) (HeaderSlices.length input) inputPointer.toNat (PersistentAlloc.rounded root 32#64).toNat (input.length%2^64) ∧
      source.memory (RequestPrefix.cursor input)=.word (PayloadPrefix.cursor input) ∧
      source.memory (byteAddress (RequestPrefix.cursor input) 72)=.word (VarList.decodedArray headerArray (HeaderSlices.bytes input)) ∧
      source.memory (byteAddress (RequestPrefix.cursor input) 80)=.word (BitVec.ofNat 64 (HeaderSlices.count input)) ∧
      OriginalScalarGlobals.Scalars source.globals ∧ AllocatedBytes.Arena (RequestPrefix.cursor input) 96 ∧ (RequestPrefix.cursor input).toNat%8=0 := by
  have memory:=LocalEffects.memory_of_erase hashed source entryFrame
  have code:=congrArg PanSemStateFiniteExact.code entryFrame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs entryFrame
  have exceptions:=congrArg PanSemStateFiniteExact.eshapes entryFrame
  have oracle:=congrArg (fun state=>state.ffi.oracle) entryFrame
  have globals:=congrArg PanSemStateFiniteExact.globals entryFrame
  change source.code=hashed.code at code
  change source.memaddrs=hashed.memaddrs at domain
  change source.eshapes=hashed.eshapes at exceptions
  change source.ffi.oracle=hashed.ffi.oracle at oracle
  change source.globals=hashed.globals at globals
  obtain ⟨headerArray,context,pointerCell,countCell⟩ := HeaderSlices.validator_context_after_hash input before copiedSource origin hashed root counts copied actual bounded prepared returned
  have current:=context.of_fields hashed source _ _ _ _ _ _ _ _ _ _ _ _ code exceptions domain oracle globals ⟨by intro query low high; rw [memory]⟩
  have transactions:=VarList.Records.count_input_bound origin input inputPointer (PersistentAlloc.rounded (PayloadPrefix.cursor input) 136#64)
    (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) actual.records
  change Payload.transactionCount input≤(input.length%2^64)/4 at transactions
  obtain ⟨witnessNumber,witnessAligned,witnessAfter,witnessRoom,siArena,siAligned,siAfter,siBefore⟩ := DecoderCall.witness_geometry input bounded transactions
  obtain ⟨rootAligned,rootAfter,rootBound,rootArena⟩ := RequestRootHashData.frontier input (DecoderSetup.entered copiedSource input) origin root actual bounded prepared.originHeap
  have payloadCell : source.memory (RequestPrefix.cursor input)=.word (PayloadPrefix.cursor input) := by
    rw [memory,returned.input.words _ (by omega) (by omega)]
    exact actual.hashes.payload
  have scalars : OriginalScalarGlobals.Scalars source.globals := by
    intro key member
    by_cases heap : key=ofString "heap_ptr"
    · subst key
      exact ⟨PersistentAlloc.rounded root 32#64,current.heapCell⟩
    · obtain ⟨word,cell⟩ := copied.scalars key member
      refine ⟨word,?_⟩
      rw [globals,returned.globals key heap,actual.globals key heap,DecoderSetup.entered_other_global copiedSource input key heap]
      exact cell
  exact ⟨headerArray,current,payloadCell,by rw [memory]; exact pointerCell,by rw [memory]; exact countCell,scalars,siArena,siAligned⟩

end InitECandidate.Solver.Input.Main.RunAttemptData

#print axioms InitECandidate.Solver.Input.Main.RunAttemptData.block_hash_names
#print axioms InitECandidate.Solver.Input.Main.RunAttemptData.entry_data
