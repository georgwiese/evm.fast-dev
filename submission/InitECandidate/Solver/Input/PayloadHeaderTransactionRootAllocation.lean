import InitECandidate.Solver.Input.PayloadHeaderFixedPrefix

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main Main.RunAttemptConstructors

def afterTransactionRoot : List CallPrefix.Action:=afterFixedHeader.drop 1
def allocatedTransactionRoot (hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  let before:=stateRootStored hashed heap
  setVarHOLFinite (ofString "txr") (.val (.word (afterOmmerHeap heap)))
    (PersistentAlloc.post {before with clock:=before.clock-1} (afterOmmerHeap heap) 32#64)

set_option maxRecDepth 100000 in
theorem transaction_root_action : afterFixedHeader=
    .scoped (ofString "txr") .one (ofString "alloc") [.const 32#64]::afterTransactionRoot := by
  simp only [afterFixedHeader,afterOmmerHash,afterOmmerMarker,afterOmmerBuffers,afterFirstStores,afterClear,afterHeader,afterReads,
    actions,parts,body,Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterTransactionRoot]
  rfl

theorem transaction_root_from_execution (input : Guest.InputBlob) (source hashed current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (installed : OriginalCode.Installed source.code)
    (layout : OmmerLayout heap) (output : OmmerHashOutput input source heap hashed)
    (execution : CallPrefix.Execution (stateRootStored hashed heap) afterFixedHeader current) :
    AllocatedBytes.Arena (afterOmmerHeap heap) 32 ∧ (afterOmmerHeap heap).toNat%8=0 ∧
      (temporaryBase heap).toNat+8≤(afterOmmerHeap heap).toNat ∧
      CallPrefix.Execution (allocatedTransactionRoot hashed heap) afterTransactionRoot current := by
  rw [transaction_root_action] at execution
  have growth:=PersistentAlloc.guards (temporaryBase heap) 8#64 layout.temporaryArena.upper
  have code:=congrArg PanSemStateFiniteExact.code output.control
  change hashed.code=source.code at code
  have actualInstalled : OriginalCode.Installed (stateRootStored hashed heap).code:=by
    change OriginalCode.Installed hashed.code
    rw [code]
    exact installed
  have args : evalListHOLFinite (stateRootStored hashed heap)
      (h:=fun address=>Classical.propDecidable ((stateRootStored hashed heap).memaddrs address)) [.const 32#64]=some (PersistentAlloc.values 32#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  obtain ⟨room,next⟩:=CallPrefix.Execution.alloc_next (source:=stateRootStored hashed heap) (target:=current)
    (ofString "txr") [.const 32#64] (afterOmmerHeap heap) 32#64 afterTransactionRoot actualInstalled args
    (output.heap input source hashed heap) growth.2.2.2.1 execution
  have previousLower:=layout.temporaryArena.lower
  have before:=growth.2.2.1
  change (temporaryBase heap).toNat+8≤(afterOmmerHeap heap).toNat at before
  exact ⟨⟨by omega,room⟩,growth.2.2.2.2,before,next⟩

theorem transaction_root_allocation (input : Guest.InputBlob) (origin initializer source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root workspace nodes stateRoot codes : BitVec 64) (counts : Nat→BitVec 64)
    (prepared : RequestRootHashData.Prepared input origin root counts)
    (ready : PayloadHeaderEntry input origin initializer source root workspace nodes stateRoot codes)
    (execution : CallPrefix.Execution source actions current) :
    ∃ heap hashed,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      workspace.toNat+40≤heap.toNat ∧ root.toNat≤heap.toNat ∧ OmmerLayout heap ∧ OmmerHashOutput input source heap hashed ∧
      AllocatedBytes.Arena (afterOmmerHeap heap) 32 ∧ (afterOmmerHeap heap).toNat%8=0 ∧
      (temporaryBase heap).toNat+8≤(afterOmmerHeap heap).toNat ∧
      CallPrefix.Execution (allocatedTransactionRoot hashed heap) afterTransactionRoot current := by
  obtain ⟨heap,hashed,heapCell,workspaceBefore,rootBefore,layout,output,afterHash⟩:=
    ommer_hash input origin initializer source current root workspace nodes stateRoot codes counts prepared ready execution
  have domain:=(output.environment input source hashed heap ready.environment).domain
  have fixed:=fixed_header_from_execution input source hashed current heap layout output domain afterHash
  exact ⟨heap,hashed,heapCell,workspaceBefore,rootBefore,layout,output,
    transaction_root_from_execution input source hashed current heap ready.state.1 layout output fixed⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.transaction_root_action
#print axioms InitECandidate.Solver.Input.PayloadHeader.transaction_root_from_execution
#print axioms InitECandidate.Solver.Input.PayloadHeader.transaction_root_allocation
