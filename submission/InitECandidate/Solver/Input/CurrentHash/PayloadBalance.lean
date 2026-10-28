import InitECandidate.Solver.Input.CurrentHash.PayloadStateCalls

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def balanceLength (input : Guest.InputBlob) (length : Nat) := (BitVec.ofNat 64 length-Payload.offsetWords input 3).toNat
def balancePointer (input : Guest.InputBlob) (blob : BitVec 64) := blob+62#64+Payload.offsetWords input 3

theorem State.balance_data {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}
    (data : State input source blob record array ch cursor chunk out zeros length start size) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) StaticFields.balanceArguments=
      some (CallNormal.tripleValues (balancePointer input blob) (BitVec.ofNat 64 (balanceLength input length)) (ch+544#64)) ∧
    balanceLength input length≤251655056 ∧ AllocatedBytes.Arena (balancePointer input blob) (balanceLength input length) := by
  obtain ⟨count,wd,countCell,p,n,countBound,exactBytes,wdArena,nEq,nBound,arena⟩ := remaining_regions data.decoded data.inputBound data.inputArena
  have pointerRead := data.field_read 64 (by decide) (by decide) _ p
  have lengthRead := data.field_read 72 (by decide) (by decide) _ n
  have outputRead : eval source (StaticFields.outputExpression 17)=some (.val (.word (ch+544#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,StaticFields.outputExpression,FixedRecord.offsetExpression,localVar,data.chunks,valueIsWord,valueWord,wordOpHOL,wordOp]
  simp only [eval] at pointerRead lengthRead outputRead
  refine ⟨?_,nBound,arena⟩
  simp only [evalListHOLFinite,StaticFields.balanceArguments,evalListHOLExact,pointerRead,lengthRead,outputRead,balancePointer,balanceLength,
    CallNormal.tripleValues,BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem State.balance_frame {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}
    (data : State input source blob record array ch cursor chunk out zeros length start size) (query : BitVec 64)
    (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32)
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_pbytes") StaticFields.balanceArguments)=(none,post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  have ready:=data.balance_data
  have bounded:=ready.2.1
  have chunksBound : PackBytes.chunks (balanceLength input length)≤134217728 := by unfold PackBytes.chunks; omega
  exact PBytesMemory.call_frame source post (balancePointer input blob) cursor chunk (ch+544#64) zeros query (balanceLength input length)
    (data.query_context query before) (by omega) chunksBound ready.2.2 (data.output_arena 17 (by decide)) (data.output_away 17 (by decide) query before)
    data.chunkCell data.chunkArena data.chunkAligned chunkAway StaticFields.balanceArguments ready.1 actual

theorem State.after_balance {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}
    (data : State input source blob record array ch cursor chunk out zeros length start size)
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_pbytes") StaticFields.balanceArguments)=(none,post)) :
    State input post blob record array ch cursor chunk out zeros length start size := by
  apply data.after_call .htr_pbytes StaticFields.balanceArguments actual
  intro query lower upper
  exact data.balance_frame query upper (data.chunk_away query lower) actual

theorem State.balance_cost {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}
    (data : State input source blob record array ch cursor chunk out zeros length start size) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_pbytes") StaticFields.balanceArguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤5*balanceLength input length+3302 := by
  have ready:=data.balance_data
  have bounded:=ready.2.1
  have chunksBound : PackBytes.chunks (balanceLength input length)≤134217728 := by unfold PackBytes.chunks; omega
  have paid := PBytesCost.call_cost source post (balancePointer input blob) (ch+544#64) (balanceLength input length)
    data.context.installed (by omega) chunksBound (some none) StaticFields.balanceArguments ready.1 result actual notTimeout
  have bound := Transactions.byte_price (balanceLength input length)
  omega

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.balance_data
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_balance
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.balance_cost

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.balance_frame
