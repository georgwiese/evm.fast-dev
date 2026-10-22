import InitECandidate.Solver.Input.PayloadHeaderInitialScopes
import InitECandidate.Solver.Input.CallPrefixAllocation

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main Main.RunAttemptConstructors

def afterHeader : List CallPrefix.Action:=afterReads.drop 1
def allocatedHeader (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  setVarHOLFinite (ofString "h") (.val (.word heap))
    (PersistentAlloc.post {(readEntry input source) with clock:=source.clock-1} heap 248#64)

set_option maxRecDepth 100000 in
theorem first_allocation_action : afterReads=
    .scoped (ofString "h") .one (ofString "alloc") [.const 248#64]::afterHeader := by
  simp only [afterReads,actions,parts,body,Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterHeader]
  rfl

/-- Derive the real first header allocation and its fresh248-byte arena
from main's reached prefix. No later allocation room or helper success is
supplied; all original local scopes remain present in the action trace. -/
theorem first_allocation (input : Guest.InputBlob) (origin initializer source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root workspace nodes stateRoot codes : BitVec 64) (counts : Nat→BitVec 64)
    (prepared : RequestRootHashData.Prepared input origin root counts)
    (ready : PayloadHeaderEntry input origin initializer source root workspace nodes stateRoot codes)
    (execution : CallPrefix.Execution source actions current) :
    ∃ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      AllocatedBytes.Arena heap 248 ∧ heap.toNat%8=0 ∧ workspace.toNat+40≤heap.toNat ∧ root.toNat≤heap.toNat ∧
      CallPrefix.Execution (allocatedHeader input source heap) afterHeader current := by
  have scopes:=initial_scopes input origin initializer source current root workspace nodes stateRoot codes counts prepared ready execution
  rw [first_allocation_action] at scopes
  obtain ⟨heap,heapCell,arena,aligned,workspaceBefore,rootBefore,inputBefore⟩:=ready.heap_geometry input origin initializer source root workspace nodes stateRoot codes
  have args : evalListHOLFinite (readEntry input source) (h:=fun address=>Classical.propDecidable ((readEntry input source).memaddrs address))
      [.const 248#64]=some (PersistentAlloc.values 248#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  obtain ⟨room,next⟩:=CallPrefix.Execution.alloc_next (source:=readEntry input source) (target:=current)
    (ofString "h") [.const 248#64] heap 248#64 afterHeader ready.state.1 args heapCell (by have bound:=arena.upper; omega) scopes
  exact ⟨heap,heapCell,⟨arena.lower,room⟩,aligned,workspaceBefore,rootBefore,next⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.first_allocation_action
#print axioms InitECandidate.Solver.Input.PayloadHeader.first_allocation
