import InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderFieldFacts

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
    ((frame.globals _ (by decide)).trans data.mptHash) nextHeap (frame.si.trans data.siLocal)
    (fun query lower upper=>frame.older query lower (by omega))

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
  exact ⟨header,⟨frame.data data before frontier,frame,buffers,frontier,before,geometry,fields,optional⟩⟩

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.HeaderFrame.data
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.physical_header
