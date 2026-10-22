import InitECandidate.Solver.Input.PayloadHeaderFirstAllocation
import InitECandidate.Solver.Input.CallPrefixCommand
import InitECandidate.Solver.WitnessRadix.ZeroNormal
import InitECandidate.Solver.MutableTable.ZeroWords

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main Main.RunAttemptConstructors

def zeroHeader : ProgHOL 64:=.call (some (none,none)) (ofString "memzero") [localVar "h",.const 248#64]
def afterClear : List CallPrefix.Action:=afterHeader.drop 1
def clearedHeader (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  let allocated:=allocatedHeader input source heap
  {allocated with memory:=Zero.finalMemory allocated.memory heap 248,clock:=allocated.clock-(Zero.price 248+1)}

set_option maxRecDepth 100000 in
theorem clearing_action : afterHeader=.command zeroHeader::afterClear := by
  simp only [afterHeader,afterReads,actions,parts,body,Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterClear,zeroHeader,localVar]
  rfl

theorem clear_from_execution (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (arena : AllocatedBytes.Arena heap 248) (aligned : heap.toNat%8=0)
    (execution : CallPrefix.Execution (allocatedHeader input source heap) afterHeader current) :
    CallPrefix.Execution (clearedHeader input source heap) afterClear current := by
  rw [clearing_action] at execution
  obtain ⟨middle,normal,next⟩:=execution.command_next zeroHeader afterClear
  let allocated:=allocatedHeader input source heap
  have hCell : allocated.locals.lookup (ofString "h")=some (.val (.word heap)):=bind_lookup_same _ _ _
  have args : evalListHOLFinite allocated (h:=fun address=>Classical.propDecidable (allocated.memaddrs address))
      [localVar "h",.const 248#64]=some (Zero.values heap 248):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,hCell,Zero.values]
  have mapped (offset : Nat) (inside : offset+8≤248) (multiple : offset%8=0) : allocated.memaddrs (byteAddress heap offset):=
    AllocatedBytes.word_mapped allocated heap 248 offset domain arena (by omega) aligned multiple
  obtain ⟨funded,same⟩:=Zero.call_normal allocated middle [localVar "h",.const 248#64] heap 248 args
    (Zero.original_code source.code installed) (by decide) (by decide) aligned mapped normal
  rw [same] at next
  exact next

theorem cleared_cells (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (slot : Nat) (inside : slot<31) :
    (clearedHeader input source heap).memory (heap+BitVec.ofNat 64 (8*slot))=.word 0#64 :=
  MutableTable.ZeroWords.final_cell source.memory heap 248 slot (by omega)

theorem cleared_older (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (arena : AllocatedBytes.Arena heap 248) (query : BitVec 64) (before : query.toNat<heap.toNat) :
    (clearedHeader input source heap).memory query=source.memory query := by
  apply Zero.final_memory_away
  intro offset inside same
  have number:=byteAddress_toNat heap offset (by have upper:=arena.upper; omega)
  have numeric:=congrArg BitVec.toNat same
  rw [number] at numeric
  omega

/-- Genuine main reaches a fully zeroed fresh header while retaining every
older input/state word and all original caller local scopes. -/
theorem clearing (input : Guest.InputBlob) (origin initializer source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root workspace nodes stateRoot codes : BitVec 64) (counts : Nat→BitVec 64)
    (prepared : RequestRootHashData.Prepared input origin root counts)
    (ready : PayloadHeaderEntry input origin initializer source root workspace nodes stateRoot codes)
    (execution : CallPrefix.Execution source actions current) :
    ∃ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      AllocatedBytes.Arena heap 248 ∧ heap.toNat%8=0 ∧ workspace.toNat+40≤heap.toNat ∧ root.toNat≤heap.toNat ∧
      CallPrefix.Execution (clearedHeader input source heap) afterClear current := by
  obtain ⟨heap,heapCell,arena,aligned,workspaceBefore,rootBefore,next⟩:=first_allocation input origin initializer source current root workspace nodes stateRoot codes counts prepared ready execution
  exact ⟨heap,heapCell,arena,aligned,workspaceBefore,rootBefore,
    clear_from_execution input source current heap ready.state.1 ready.environment.domain arena aligned next⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.clearing_action
#print axioms InitECandidate.Solver.Input.PayloadHeader.clear_from_execution
#print axioms InitECandidate.Solver.Input.PayloadHeader.cleared_cells
#print axioms InitECandidate.Solver.Input.PayloadHeader.cleared_older
#print axioms InitECandidate.Solver.Input.PayloadHeader.clearing
