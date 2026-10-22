import InitECandidate.Solver.Input.MainRunAttemptTransactions
import InitECandidate.Solver.Input.RunAttemptPayloadHeaderCallTrace

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

structure PayloadHeaderEntry (input : Guest.InputBlob)
    (origin initializer entry : PanSemStateFiniteExact 64 Guest.HostMemory) (root workspace nodes stateRoot codes : BitVec 64) : Prop where
  state : Mpt.StateInit.Output input initializer entry workspace nodes stateRoot codes
  environment : Keccak256.Environment entry 2713714976#64 2713715176#64
  si : entry.locals.lookup (ofString "si")=some (.val (.word (RequestPrefix.cursor input)))
  inputFrame : HashInput.Frame origin entry inputPointer.toNat root.toNat
  rootBefore : root.toNat≤workspace.toNat
  rootLower : inputPointer.toNat≤root.toNat
  mpt : MptWorkspace.Bindings entry

/-- Fresh header work starts beyond the genuine old decoder/state region.
The real current heap remains an aligned ordinary arena frontier. -/
theorem PayloadHeaderEntry.heap_geometry (input : Guest.InputBlob)
    (origin initializer entry : PanSemStateFiniteExact 64 Guest.HostMemory) (root workspace nodes stateRoot codes : BitVec 64)
    (ready : PayloadHeaderEntry input origin initializer entry root workspace nodes stateRoot codes) :
    ∃ heap,entry.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      AllocatedBytes.Arena heap 0 ∧ heap.toNat%8=0 ∧ workspace.toNat+40≤heap.toNat ∧
      root.toNat≤heap.toNat ∧ inputPointer.toNat≤heap.toNat := by
  obtain ⟨heap,cell,arena,aligned,afterWorkspace⟩:=ready.state.heap_geometry input initializer entry workspace nodes stateRoot codes
  have afterRoot : root.toNat≤heap.toNat:=ready.rootBefore.trans (by omega)
  exact ⟨heap,cell,arena,aligned,afterWorkspace,afterRoot,ready.rootLower.trans afterRoot⟩

def payloadHeaderEntryPrice (input : Guest.InputBlob):=transactionPrecheckPrice input+1

/-- Actual unchanged main reaches the real payload_header callee with its
initialized state and decoded input. The original caller/child remainder
is retained, including every earlier stopped outcome and call failure. -/
theorem payload_header_entry_of_actual (input : Guest.InputBlob)
    (before copiedSource origin hashed source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts) (returned : RequestHash.Returned input origin hashed root)
    (entryFrame : LocalEffects.erase source=LocalEffects.erase hashed)
    (siCell : source.locals.lookup (ofString "si")=some (.val (.word (RequestPrefix.cursor input))))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source RunAttempt.body=(outcome,post)) :
    source.clock-post.clock≤payloadHeaderEntryPrice input ∨
      ∃ initializer caller entry target inner : PanSemStateFiniteExact 64 Guest.HostMemory,
      ∃ workspace nodes stateRoot codes : BitVec 64,∃ childResult,
        PayloadHeaderEntry input origin initializer entry root workspace nodes stateRoot codes ∧
        entry.clock≤source.clock ∧ source.clock-entry.clock≤payloadHeaderEntryPrice input ∧ post.clock=inner.clock ∧
        evaluateHOLFiniteState entry PayloadHeader.body=(childResult,target) ∧
        RunAttempt.PayloadHeaderResumes caller target inner childResult outcome := by
  rcases transactions_of_actual input before copiedSource origin hashed source post root counts copied actual bounded prepared returned entryFrame siCell outcome run with stopped|reached
  · exact Or.inl (stopped.trans (Nat.le_add_right _ _))
  · obtain ⟨initializer,caller,inner,workspace,nodes,stateRoot,codes,output,environment,forward,spent,endpoint,remaining,bindings,inputFrame,rootBefore,mpt⟩:=reached
    rcases RunAttempt.payload_header_call_trace caller inner (RequestPrefix.cursor input) output.1 bindings.si outcome remaining with stopped|observed
    · exact Or.inl (by unfold payloadHeaderEntryPrice; rw [endpoint]; omega)
    · obtain ⟨entry,target,childResult,frame,clock,entrySI,childRun,resumes⟩:=observed
      have currentOutput:=output.of_erase input initializer caller entry workspace nodes stateRoot codes frame
      have memory:=LocalEffects.memory_of_erase caller entry frame
      have currentInput:=inputFrame.of_memory origin caller entry _ _ memory
      have sameDomain:=congrArg PanSemStateFiniteExact.memaddrs frame
      have sameCode:=congrArg PanSemStateFiniteExact.code frame
      have sameOracle:=congrArg (fun state=>state.ffi.oracle) frame
      have currentEnvironment:=Keccak256.Environment.of_fields caller entry 2713714976#64 2713715176#64 environment
        sameDomain sameCode sameOracle (by intro key other; have sameGlobal:=congrArg (fun state=>state.globals.lookup key) frame; exact sameGlobal)
      have currentMpt:=MptWorkspace.Bindings.of_erase caller entry mpt frame
      have rootLower : inputPointer.toNat≤root.toNat:=by
        have lower:=prepared.layout.siLower
        have beforeRoot:=prepared.layout.siBefore
        omega
      exact Or.inr ⟨initializer,caller,entry,target,inner,workspace,nodes,stateRoot,codes,childResult,
        ⟨currentOutput,currentEnvironment,entrySI,currentInput,rootBefore,rootLower,currentMpt⟩,by omega,by unfold payloadHeaderEntryPrice; omega,endpoint,childRun,resumes⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.payload_header_entry_of_actual
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.PayloadHeaderEntry.heap_geometry
