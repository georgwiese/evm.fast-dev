import InitECandidate.Solver.Input.PayloadHeaderRemainingBuffers

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main Main.RunAttemptConstructors

structure HeaderBuffers (heap : BitVec 64) : Prop where
  ommer : OmmerLayout heap
  transactions : AllocatedBytes.Arena (afterOmmerHeap heap) 32
  nonce : AllocatedBytes.Arena (zeroBase heap) 8
  withdrawals : AllocatedBytes.Arena (withdrawalBase heap) 32
  requests : AllocatedBytes.Arena (requestsBase heap) 32
  balance : AllocatedBytes.Arena (balanceBase heap) 32

/-- The real main-derived prefix produces the entire physical header and
all seven auxiliary buffers at its actual block_rlp_length caller. -/
theorem complete_header_from_execution (input : Guest.InputBlob) (origin initializer source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root workspace nodes stateRoot codes : BitVec 64) (counts : Nat→BitVec 64)
    (prepared : RequestRootHashData.Prepared input origin root counts)
    (ready : PayloadHeaderEntry input origin initializer source root workspace nodes stateRoot codes)
    (execution : CallPrefix.Execution source actions current) :
    ∃ heap hashed,∃ words : RlpWrite.U256Value.Words,
      source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      workspace.toNat+40≤heap.toNat ∧ root.toNat≤heap.toNat ∧ HeaderBuffers heap ∧ OmmerHashOutput input source heap hashed ∧
      HeaderFrame input source heap current ∧ HeapFrontier current heap (headerFrontier heap) ∧
      current=completeHeader input source hashed heap words := by
  obtain ⟨heap,hashed,words,heapCell,workspaceBefore,rootBefore,layout,output,txrArena,zeroArena,feeFrame,feeFrontier,feeTrace⟩:=
    base_fee_reached input origin initializer source current root workspace nodes stateRoot codes counts prepared ready execution
  obtain ⟨wrArena,wrFrame,wrFrontier,wrTrace⟩:=withdrawal_allocation_from_execution input source hashed current heap words ready.state.1 feeFrame feeFrontier feeTrace
  obtain ⟨fieldsFrame,fieldsFrontier,fieldsTrace⟩:=withdrawal_fields_from_execution input origin source hashed current heap root words counts
    prepared rootBefore ready.inputFrame ready.si layout ready.environment.domain wrFrame wrFrontier wrTrace
  obtain ⟨rhArena,bhArena,finalFrame,finalFrontier,same⟩:=remaining_buffers_from_execution input origin source hashed current heap root words counts
    prepared rootBefore ready.state.1 layout ready.environment.domain fieldsFrame fieldsFrontier fieldsTrace
  rw [←same] at finalFrame finalFrontier
  exact ⟨heap,hashed,words,heapCell,workspaceBefore,rootBefore,⟨layout,txrArena,zeroArena,wrArena,rhArena,bhArena⟩,
    output,finalFrame,finalFrontier,same⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.complete_header_from_execution
