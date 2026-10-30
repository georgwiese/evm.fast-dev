import InitECandidate.Solver.Input.CurrentVerify.BlockLengthCall
import InitECandidate.Solver.Input.CurrentVerify.DataMetadata
import InitECandidate.Solver.Input.HeaderEncoding.FieldFrame

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual normal length result leaves the complete physical header,
input/transaction/witness data and original heap available to the next
payload caller. This uses the observed body frame, not a future helper. -/
theorem PhysicalHeader.after_length {input : Guest.InputBlob} {source current child : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header)
    (value : ValueHOL 64) (metadata : MemoryMetadata.erase child=MemoryMetadata.erase current)
    (memory : HeaderEncoding.OldMemory child.memory current.memory (headerFrontier header)) :
    PhysicalHeader input source (CallNormal.continuationEntry current child "bl" value) pointer si record gasWord boundary header := by
  let ready:=CallNormal.continuationEntry current child "bl" value
  have frame : MemoryMetadata.erase ready=MemoryMetadata.erase current:=metadata
  have domain:=MemoryMetadata.domain frame
  have endian:=MemoryMetadata.endian frame
  have code:=MemoryMetadata.code frame
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change ready.globals=current.globals at globals
  have before : boundary≤(headerFrontier header).toNat:=by have a:=physical.before; have b:=physical.frontier.afterHeader; omega
  have siCell : ready.locals.lookup (ofString "si")=some (.val (.word si)):=
    (CallNormal.continuation_lookup_other current child "bl" "si" value (by decide)).trans physical.data.siLocal
  have data:=physical.data.of_metadata frame siCell (fun query lower upper=>memory query (by omega))
  have headerFrame : HeaderFrame source ready pointer record header:=⟨code.trans physical.frame.code,domain.trans physical.frame.domain,endian.trans physical.frame.endian,
    fun key different=>by rw [globals]; exact physical.frame.globals key different,
    (CallNormal.continuation_lookup_other current child "bl" "h" value (by decide)).trans physical.frame.header,
    (CallNormal.continuation_lookup_other current child "bl" "raw" value (by decide)).trans physical.frame.raw,
    (CallNormal.continuation_lookup_other current child "bl" "pl" value (by decide)).trans physical.frame.payload,
    (CallNormal.continuation_lookup_other current child "bl" "si" value (by decide)).trans physical.frame.si,
    fun query lower upper=>(memory query (by have h:=physical.frontier.afterHeader; omega)).trans (physical.frame.older query lower upper)⟩
  have cells (offset : Nat) (inside : offset≤240) : ready.memory (HeaderEncoding.address header offset)=current.memory (HeaderEncoding.address header offset):=by
    apply memory
    rw [physical.geometry.header_address header (headerFrontier header) offset inside]
    have earlier:=physical.geometry.headerBefore
    omega
  exact ⟨data,headerFrame,physical.buffers,physical.frontier.of_globals current ready header (headerFrontier header) globals,physical.before,physical.geometry,
    fun field member=>HeaderEncoding.FieldFacts.of_cells current.memory ready.memory header field cells (physical.fields field member),
    fun field member=>HeaderEncoding.FieldFacts.of_cells current.memory ready.memory header field cells (physical.optional field member),
    ⟨(CallNormal.continuation_lookup_other current child "bl" "txr" value (by decide)).trans physical.locals.transactions,
      (CallNormal.continuation_lookup_other current child "bl" "wr" value (by decide)).trans physical.locals.withdrawals,
      (CallNormal.continuation_lookup_other current child "bl" "rh" value (by decide)).trans physical.locals.requests,
      (CallNormal.continuation_lookup_other current child "bl" "bh" value (by decide)).trans physical.locals.balance⟩,physical.entryHeap⟩

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.PhysicalHeader.after_length
