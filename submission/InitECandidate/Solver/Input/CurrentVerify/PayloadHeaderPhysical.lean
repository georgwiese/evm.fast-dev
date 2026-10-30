import InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderFieldFacts
import InitECandidate.Solver.Mpt.CurrentStateInitMemoryContext

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The whole original decoded input remains available at the real next
caller. The actual heap frontier and protected memory supply this contract. -/
theorem HeaderFrame.data {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord heap cursor : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) (before : boundary+32≤heap.toNat)
    (frame : HeaderFrame source current pointer record heap) (frontier : HeapFrontier current heap cursor) :
    Data input current pointer si record gasWord boundary := by
  have arena : CurrentStartup.ArenaState current:=
    ⟨(frame.globals _ (by decide)).trans data.arena.scratch,(frame.globals _ (by decide)).trans data.arena.frame,
      frame.domain.trans data.arena.domain,by rw [frame.code]; exact data.arena.code⟩
  have nextHeap : NormalHeapEffects.AtLeast (boundary+32) current:=
    ⟨cursor,frontier.cell,by have afterHeader:=frontier.afterHeader; omega,frontier.bounded,frontier.aligned⟩
  exact data.of_interval arena (frame.endian.trans data.little) (frame.environment source current pointer record heap data.keccak)
    ((frame.globals _ (by decide)).trans data.mptHash) ((frame.globals _ (by decide)).trans data.mptKey) ((frame.globals _ (by decide)).trans data.mptEmpty)
    ((frame.globals _ (by decide)).trans data.shaState) ((frame.globals _ (by decide)).trans data.shaPad) ((frame.globals _ (by decide)).trans data.u256) nextHeap (frame.si.trans data.siLocal)
    (fun query lower upper=>frame.older query lower (by omega))

/-- The four actual scoped root-buffer bindings remain live through the
completed header prefix and the later block-length caller restoration. -/
structure BufferLocals (current : PanSemStateFiniteExact 64 Guest.HostMemory) (header : BitVec 64) : Prop where
  transactions : current.locals.lookup (ofString "txr")=some (.val (.word (afterOmmerHeap header)))
  withdrawals : current.locals.lookup (ofString "wr")=some (.val (.word (withdrawalBase header)))
  requests : current.locals.lookup (ofString "rh")=some (.val (.word (requestsBase header)))
  balance : current.locals.lookup (ofString "bh")=some (.val (.word (balanceBase header)))

theorem complete_header_buffer_locals (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record header : BitVec 64) (words : RlpWrite.U256Value.Words) :
    BufferLocals (completeHeader source hashed pointer record header words) header := by
  constructor <;>
    simp [completeHeader,balancePointerStored,allocatedBalance,requestsPointerStored,allocatedRequests,beforeRequests,
      withdrawalScalarsStored,withdrawalPointerStored,allocatedWithdrawal,allocatedField,baseFeeStored,wideStored,feeEntry,
      zeroPointerStored,clearedZero,allocatedZero,beforeZero,scalarPrefixStored,scalarFields,withdrawalScalarFields,
      payloadFieldsStored,wideZeroStored,bloomPointerStored,receiptsPointerStored,transactionPointerStored,allocatedTransactionRoot,
      putHeader,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]

/-- Physical inputs at the actual block-length caller. Geometry describes
readable byte ranges; each allocator's persistent room is derived separately
from that allocator's genuine successful execution. -/
structure PhysicalHeader (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si record gasWord : BitVec 64) (boundary : Nat) (header : BitVec 64) : Prop where
  data : Data input current pointer si record gasWord boundary
  frame : HeaderFrame source current pointer record header
  buffers : HeaderBuffers header
  frontier : HeapFrontier current header (headerFrontier header)
  before : boundary+32≤header.toNat
  geometry : HeaderEncoding.Geometry header (headerFrontier header)
  fields : ∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts current.memory header field
  optional : ∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts current.memory header field
  locals : BufferLocals current header
  entryHeap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word header))

/-- A reached unchanged prefix derives the complete actual physical encoder
entry, while retaining all earlier transaction/input/witness data for the
block-length and subsequent main calls. -/
theorem physical_header {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) (execution : CallPrefix.Execution source actions current) :
    ∃ header,PhysicalHeader input source current pointer si record gasWord boundary header := by
  obtain ⟨header,hashed,words,heapCell,before,buffers,output,frame,frontier,same⟩:=complete_header_from_execution data execution
  have lower : 2701134824≤header.toNat:=by have recordLower:=data.recordInside.1; have recordBefore:=data.recordInside.2; omega
  have cells (slot : Fin 31) : current.memory (header+BitVec.ofNat 64 (8*slot.val))=.word (headerWord source pointer record header words slot):=by
    rw [same]
    exact complete_header_cells source hashed pointer record header words buffers output lower slot
  obtain ⟨fields,optional⟩:=header_field_facts words data buffers current.memory cells
  have geometry : HeaderEncoding.Geometry header (headerFrontier header):=
    ⟨buffers.ommer.headerArena.lower,buffers.ommer.headerAligned,frontier.afterHeader,frontier.aligned,
      by have upper:=frontier.bounded; omega⟩
  exact ⟨header,⟨frame.data data before frontier,frame,buffers,frontier,before,geometry,fields,optional,(by rw [same]; exact complete_header_buffer_locals source hashed pointer record header words),heapCell⟩⟩

/-- Whole-header preservation of the actual entering heap, state globals
and earlier persistent state/input memory above the640byte arithmetic
workspace. Temporary workspaces below this
interval and the withdrawal-array destination may change. -/
structure StateFrame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (header : BitVec 64) : Prop where
  entryHeap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word header))
  globals : ∀ key : Flapjack.Pancake.PanLang.MlS,key≠ofString "heap_ptr"→key≠ofString "wd_rlp_slices"→target.globals.lookup key=source.globals.lookup key
  older : ∀ query : BitVec 64,2701135464≤query.toNat→query.toNat<header.toNat→target.memory query=source.memory query

def PreservesState (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (header : BitVec 64) : Prop :=
  ∀ origin,StateFrame origin source header→StateFrame origin target header

theorem StateFrame.after {origin source target : PanSemStateFiniteExact 64 Guest.HostMemory} {header : BitVec 64}
    (frame : StateFrame origin source header)
    (globals : ∀ key : Flapjack.Pancake.PanLang.MlS,key≠ofString "heap_ptr"→key≠ofString "wd_rlp_slices"→target.globals.lookup key=source.globals.lookup key)
    (older : ∀ query : BitVec 64,2701135464≤query.toNat→query.toNat<header.toNat→target.memory query=source.memory query) :
    StateFrame origin target header :=
  ⟨frame.entryHeap,fun key a b=>(globals key a b).trans (frame.globals key a b),fun query a b=>(older query a b).trans (frame.older query a b)⟩

theorem StateFrame.of_erase {origin source target : PanSemStateFiniteExact 64 Guest.HostMemory} {header : BitVec 64}
    (frame : StateFrame origin source header) (same : LocalEffects.erase target=LocalEffects.erase source) :
    StateFrame origin target header := by
  have globals:=congrArg PanSemStateFiniteExact.globals same
  change target.globals=source.globals at globals
  have memory:=LocalEffects.memory_of_erase source target same
  exact ⟨frame.entryHeap,by intro key a b; rw [globals]; exact frame.globals key a b,
    by intro query a b; rw [memory]; exact frame.older query a b⟩

theorem PhysicalHeader.state_frame {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header) : StateFrame source current header :=
  ⟨physical.entryHeap,fun key a _=>physical.frame.globals key a,fun query a b=>physical.frame.older query (by omega) b⟩

theorem StateFrame.state_records {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {header frontier ws bs : BitVec 64}
    (frame : StateFrame source target header) (records : Mpt.StateInit.MemoryContext source frontier ws bs)
    (arena : CurrentStartup.ArenaState target) (afterHeader : NormalHeapEffects.AtLeast header.toNat target) :
    Mpt.StateInit.MemoryContext target frontier ws bs := by
  obtain ⟨old,oldCell,oldLower,oldBound,oldAligned⟩:=records.afterBs
  have sameHeap : old=header:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (oldCell.symm.trans frame.entryHeap)))
  subst old
  obtain ⟨heap,cell,lower,bounded,aligned⟩:=afterHeader
  exact records.of_fields arena ⟨heap,cell,by omega,bounded,aligned⟩
    ((frame.globals _ (by decide) (by decide)).trans records.wsCell)
    ((frame.globals _ (by decide) (by decide)).trans records.bsCell)

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.HeaderFrame.data
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.physical_header

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.complete_header_buffer_locals
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.StateFrame.after
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.StateFrame.of_erase
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.PhysicalHeader.state_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.StateFrame.state_records
