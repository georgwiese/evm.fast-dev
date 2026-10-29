import InitECandidate.Solver.Input.CurrentVerify.BlockLengthData
import InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderPhysical
import InitECandidate.Solver.Input.CurrentRlp.BlockCall

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The main-derived physical header and decoded input instantiate the
complete current block-length bound on every callee outcome. -/
theorem length_body_cost {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hdr : callee.lookup (ofString "hdr")=some (.val (.word header)))
    (pl : callee.lookup (ofString "pl")=some (.val (.word record))) :
    (callEntryStateHOLFinite current callee).clock-
      (evaluateHOLFiniteState (callEntryStateHOLFinite current callee) CurrentRlp.BlockLength.body).2.clock≤396930025 := by
  obtain ⟨array,start,size,inputs⟩:=physical.data.block_inputs
  let entry:=callEntryStateHOLFinite current callee
  have data:=RlpLength.Block.Data.of_fields current entry input pointer array record start size (withdrawalStart input) (Payload.withdrawalCount input) rfl rfl rfl inputs.data
  have before : boundary≤(headerFrontier header).toNat:=by have a:=physical.before; have b:=physical.frontier.afterHeader; omega
  have price:=CurrentRlp.BlockLength.body_cost entry input pointer array record header (headerFrontier header) start size (withdrawalStart input) (Payload.withdrawalCount input)
    physical.data.arena.domain data physical.geometry (by have earlier:=inputs.inputBefore; omega) (by intro nonzero; have earlier:=inputs.arrayBefore; omega)
    (by intro offset member; have earlier:=inputs.cellsBefore offset member; omega) physical.data.arena.code hdr pl physical.frontier.cell physical.frontier.bounded physical.fields physical.optional
  have count:=inputs.txCount
  have wd:=inputs.wdCount
  have bound:=inputs.inputBound
  unfold CurrentRlp.BlockLength.price at price
  change entry.clock-(evaluateHOLFiniteState entry CurrentRlp.BlockLength.body).2.clock≤396930025
  omega

/-- A genuine normal current block-length callee supplies its real size,
restored heap and protected earlier input/header memory at this actual caller. -/
theorem length_body_normal {input : Guest.InputBlob} {source current target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (hdr : callee.lookup (ofString "hdr")=some (.val (.word header)))
    (pl : callee.lookup (ofString "pl")=some (.val (.word record)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState (callEntryStateHOLFinite current callee) CurrentRlp.BlockLength.body=(some (.returned value),target)) :
    ∃ encoded,25*Payload.withdrawalCount input≤encoded ∧ encoded≤817879876+57*Payload.withdrawalCount input ∧
      (BitVec.ofNat 64 encoded).toNat=encoded ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧
      MemoryMetadata.erase target=MemoryMetadata.erase current ∧ HeaderEncoding.OldMemory target.memory current.memory (headerFrontier header) := by
  obtain ⟨array,start,size,inputs⟩:=physical.data.block_inputs
  let entry:=callEntryStateHOLFinite current callee
  have data:=RlpLength.Block.Data.of_fields current entry input pointer array record start size (withdrawalStart input) (Payload.withdrawalCount input) rfl rfl rfl inputs.data
  have before : boundary≤(headerFrontier header).toNat:=by have a:=physical.before; have b:=physical.frontier.afterHeader; omega
  exact CurrentRlp.BlockLength.body_normal entry target input pointer array record header (headerFrontier header) start size (withdrawalStart input) (Payload.withdrawalCount input)
    physical.data.arena.domain data physical.geometry (by have earlier:=inputs.inputBefore; omega) (by intro nonzero; have earlier:=inputs.arrayBefore; omega)
    (by intro offset member; have earlier:=inputs.cellsBefore offset member; omega) physical.data.arena.code hdr pl physical.frontier.cell physical.frontier.bounded physical.fields physical.optional value normal

def lengthActions : List CallPrefix.Action:=[.scoped (ofString "bl") .one (ofString "block_rlp_length") [localVar "h",localVar "pl"]]

theorem length_program : lengthCall=CallPrefix.program lengthActions PayloadHeader.afterLength:=by
  change PayloadHeader.lengthCall=CallPrefix.program lengthActions PayloadHeader.afterLength
  rw [PayloadHeader.length_call_shape]
  rfl

theorem length_sink_cost {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header) :
    current.clock-(evaluateHOLFiniteState current (CallPrefix.program lengthActions .skip)).2.clock≤396930026 := by
  obtain ⟨callee,called,hdr,pl⟩:=CurrentRlp.BlockLength.environment current.code.lookup header record
    (CurrentRlp.BlockLength.original_code current.code physical.data.arena.code)
  have args : evalListHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) [localVar "h",localVar "pl"]=
      some [.val (.word header),.val (.word record)]:=by
    have hCell:=physical.frame.header
    have plCell:=physical.frame.payload
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,hCell,plCell]
  exact ClockCost.scoped_current current (ofString "bl") .one (ofString "block_rlp_length") [localVar "h",localVar "pl"] _
    CurrentRlp.BlockLength.body .skip callee .one 396930025 0 args called (length_body_cost physical callee hdr pl) (ClockCost.skip current.code)

/-- The actual payload-header block-length call either stops within its
finite price or reaches its genuine next caller with that same bounded cost. -/
theorem length_trace {input : Guest.InputBlob} {source current post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header)
    (outcome : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState current lengthCall=(outcome,post)) :
    (current.clock-post.clock≤396930026 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ continued inner,CallPrefix.Execution current lengthActions continued ∧ continued.clock≤current.clock ∧ current.clock-continued.clock≤396930026 ∧
        post.clock=inner.clock ∧ evaluateHOLFiniteState continued PayloadHeader.afterLength=(outcome,inner) := by
  rw [length_program] at actual
  rcases CallPrefix.priced_trace current post lengthActions PayloadHeader.afterLength 396930026 (length_sink_cost physical) outcome actual with stopped|reached
  · refine Or.inl ⟨stopped.1,?_⟩
    intro value
    rw [stopped.2]
    exact NoReturn.scoped_call _ _ _ _ _ NoReturn.skip current value
  · exact Or.inr reached

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.length_body_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.length_body_normal
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.length_program
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.length_sink_cost
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.length_trace
