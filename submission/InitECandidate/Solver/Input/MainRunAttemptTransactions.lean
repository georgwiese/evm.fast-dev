import InitECandidate.Solver.Input.MainRunAttemptInitialized
import InitECandidate.Solver.Input.RunAttemptTransactionData
import InitECandidate.Solver.Mpt.StateInitOutputFrame

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def transactionPrecheckPrice (input : Guest.InputBlob) := initializationPrice input+Payload.transactionCount input

/-- Genuine original main through initialization and the empty-transaction
scan. Its linear count comes from the real decoder, while the actual trie,
eight tables, empty journal and old input survive to payload_header. -/
theorem transactions_of_actual (input : Guest.InputBlob)
    (before copiedSource origin hashed source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts) (returned : RequestHash.Returned input origin hashed root)
    (entryFrame : LocalEffects.erase source=LocalEffects.erase hashed)
    (siCell : source.locals.lookup (ofString "si")=some (.val (.word (RequestPrefix.cursor input))))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source RunAttempt.body=(outcome,post)) :
    source.clock-post.clock≤transactionPrecheckPrice input ∨
      ∃ entry current inner : PanSemStateFiniteExact 64 Guest.HostMemory,∃ workspace nodes stateRoot codes : BitVec 64,
        Mpt.StateInit.Output input entry current workspace nodes stateRoot codes ∧
        Keccak256.Environment current 2713714976#64 2713715176#64 ∧
        current.clock≤source.clock ∧ source.clock-current.clock≤transactionPrecheckPrice input ∧ post.clock=inner.clock ∧
        evaluateHOLFiniteState current RunAttempt.afterTransactionScan=(outcome,inner) ∧ CallerLocals input current ∧
        HashInput.Frame origin current inputPointer.toNat root.toNat ∧ root.toNat≤workspace.toNat ∧ MptWorkspace.Bindings current := by
  rcases initialized_of_actual input before copiedSource origin hashed source post root counts copied actual bounded prepared returned entryFrame siCell outcome run with stopped|reached
  · exact Or.inl (stopped.trans (Nat.le_add_right _ _))
  · obtain ⟨entry,initialized,initInner,workspace,nodes,stateRoot,codes,output,environment,forward,spent,endpoint,continued,bindings,inputFrame,rootBefore,mpt⟩:=reached
    have domain : initialized.memaddrs=InitE.ordinaryDomain:=output.2.2.1.domain
    obtain ⟨arrayRead,countRead,countBound,countSmall⟩:=transaction_reads input origin initialized root counts prepared inputFrame domain bindings
    rcases RunAttempt.transaction_prefix_trace initialized initInner (PayloadHashData.description input).transactions
      (Payload.transactionCount input) countSmall arrayRead countRead outcome continued with stopped|scanned
    · exact Or.inl (by unfold transactionPrecheckPrice; rw [endpoint]; omega)
    · obtain ⟨current,inner,frame,locals,scanForward,scanSpent,scanEndpoint,remaining⟩:=scanned
      have currentOutput:=output.of_erase input entry initialized current workspace nodes stateRoot codes frame
      have memory:=LocalEffects.memory_of_erase initialized current frame
      have currentInput:=inputFrame.of_memory origin initialized current _ _ memory
      have currentBindings : CallerLocals input current:=by
        constructor
        · rw [locals (ofString "si") (by decide)]
          exact (bind_lookup_other _ "i" "si" _ (by decide)).trans
            ((bind_lookup_other _ "ntx" "si" _ (by decide)).trans
              ((bind_lookup_other _ "txs" "si" _ (by decide)).trans bindings.si))
        · rw [locals (ofString "pl") (by decide)]
          exact (bind_lookup_other _ "i" "pl" _ (by decide)).trans
            ((bind_lookup_other _ "ntx" "pl" _ (by decide)).trans
              ((bind_lookup_other _ "txs" "pl" _ (by decide)).trans bindings.payload))
      have sameDomain:=congrArg PanSemStateFiniteExact.memaddrs frame
      have sameCode:=congrArg PanSemStateFiniteExact.code frame
      have sameOracle:=congrArg (fun state=>state.ffi.oracle) frame
      have currentEnvironment:=Keccak256.Environment.of_fields initialized current 2713714976#64 2713715176#64 environment
        sameDomain sameCode sameOracle (by intro key other; have sameGlobal:=congrArg (fun state=>state.globals.lookup key) frame; exact sameGlobal)
      have currentMpt:=MptWorkspace.Bindings.of_erase initialized current mpt frame
      exact Or.inr ⟨entry,current,inner,workspace,nodes,stateRoot,codes,currentOutput,currentEnvironment,
        scanForward.trans forward,by unfold transactionPrecheckPrice; omega,endpoint.trans scanEndpoint,remaining,currentBindings,currentInput,rootBefore,currentMpt⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.transactions_of_actual
