import InitECandidate.Solver.Input.CurrentVerify.BlockLengthReturned
import InitECandidate.Solver.Input.CallPrefixScopedActual

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The real reached length action supplies its own actual normal child;
from that execution we derive the returned length and physical next caller. -/
theorem length_reached {input : Guest.InputBlob} {source current continued : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord header : BitVec 64} {boundary : Nat}
    (physical : PhysicalHeader input source current pointer si record gasWord boundary header)
    (execution : CallPrefix.Execution current lengthActions continued) :
    ∃ encoded,25*Payload.withdrawalCount input≤encoded ∧ (BitVec.ofNat 64 encoded).toNat=encoded ∧
      continued.locals.lookup (ofString "bl")=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
      PhysicalHeader input source continued pointer si record gasWord boundary header := by
  obtain ⟨callee,called,hdr,pl⟩:=CurrentRlp.BlockLength.environment current.code.lookup header record
    (CurrentRlp.BlockLength.original_code current.code physical.data.arena.code)
  have args : evalListHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) [localVar "h",localVar "pl"]=
      some [.val (.word header),.val (.word record)]:=by
    have hCell:=physical.frame.header
    have plCell:=physical.frame.payload
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,hCell,plCell]
  obtain ⟨child,value,run,endpoint⟩:=CallPrefix.Reaches.scoped_known (ofString "bl") .one (ofString "block_rlp_length") [localVar "h",localVar "pl"] _
    CurrentRlp.BlockLength.body callee .one args called execution.singleton
  obtain ⟨encoded,lower,upper,number,answer,metadata,memory⟩:=length_body_normal physical callee hdr pl value run
  have next:=physical.after_length value metadata memory
  rw [endpoint]
  refine ⟨encoded,lower,number,?_,next⟩
  simp [setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,answer]

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.length_reached
