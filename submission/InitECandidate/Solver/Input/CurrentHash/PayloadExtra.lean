import InitECandidate.Solver.Input.CurrentHash.PayloadStateCalls

set_option maxRecDepth 100000

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def extraLength (input : Guest.InputBlob) := Guest.GasLimit.le32 input 566-540

theorem State.extra_data {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}
    (data : State input source blob record array ch cursor chunk out zeros length start size) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) StaticFields.extraArguments=
      some (BytesCallCost.values .list (blob+602#64) 1#64 (ch+320#64) (extraLength input)) ∧
    extraLength input≤32 ∧ AllocatedBytes.Arena (blob+602#64) (extraLength input) := by
  have prefixImage:=data.decoded.transactions.hashPrefix
  have pointerRead := data.field_read 16 (by decide) (by decide) _ prefixImage.extraPointer
  have lengthRead := data.field_read 24 (by decide) (by decide) _ prefixImage.extraLength
  have outputRead : eval source (StaticFields.outputExpression 10)=some (.val (.word (ch+320#64))) := by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,StaticFields.outputExpression,FixedRecord.offsetExpression,localVar,data.chunks,valueIsWord,valueWord,wordOpHOL,wordOp]
  simp only [eval] at pointerRead lengthRead outputRead
  have ranges := offset_ranges data.decoded data.inputBound
  have offset := ranges.2.2.1 1 (by decide)
  have rawSmall:=RawScalar.le32_lt input 566
  have number : (Payload.offsetWords input 1).toNat=Guest.GasLimit.le32 input 566 := by
    change (BitVec.ofNat 64 (Guest.GasLimit.le32 input 566)).toNat=Guest.GasLimit.le32 input 566
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : Guest.GasLimit.le32 input 566<2^64)]
  rw [number] at offset
  refine ⟨?_,prefixImage.extraBound,AllocatedBytes.Arena.subrange blob (input.length%2^64) 602 (extraLength input) data.inputArena (by unfold extraLength; omega)⟩
  simp only [evalListHOLFinite,StaticFields.extraArguments,evalListHOLExact,pointerRead,lengthRead,outputRead,evalHOLExact,BytesCallCost.values,extraLength]

theorem State.extra_frame {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}
    (data : State input source blob record array ch cursor chunk out zeros length start size) (query : BitVec 64)
    (before : query.toNat<ch.toNat) (chunkAway : CopyGeneral.Away chunk query 32)
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_bytes_list") StaticFields.extraArguments)=(none,post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  have ready:=data.extra_data
  have bound:=ready.2.1
  exact BytesCallMemory.frame .list source post (blob+602#64) cursor 1#64 (ch+320#64) zeros chunk query (extraLength input) 0
    (data.query_context query before) (by omega) (by decide) (by unfold PackBytes.chunks; omega) (by intro; decide)
    ready.2.2 (data.output_arena 10 (by decide)) (by intro impossible; cases impossible) (data.output_away 10 (by decide) query before)
    (by intro; exact ⟨data.chunkCell,data.chunkArena,data.chunkAligned,chunkAway⟩) StaticFields.extraArguments ready.1 actual

theorem State.after_extra {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}
    (data : State input source blob record array ch cursor chunk out zeros length start size)
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_bytes_list") StaticFields.extraArguments)=(none,post)) :
    State input post blob record array ch cursor chunk out zeros length start size := by
  apply data.after_call .htr_bytes_list StaticFields.extraArguments actual
  intro query lower upper
  exact data.extra_frame query upper (data.chunk_away query lower) actual

theorem State.extra_cost {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob record array ch cursor chunk out zeros : BitVec 64} {length start size : Nat}
    (data : State input source blob record array ch cursor chunk out zeros length start size) (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_bytes_list") StaticFields.extraArguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤270 := by
  have ready:=data.extra_data
  have bound:=ready.2.1
  have price:=BytesCallCost.cost .list source post (blob+602#64) 1#64 (ch+320#64) (extraLength input) 0 data.context.installed
    (by omega) (by decide) (by unfold PackBytes.chunks; omega) (by intro; decide) (some none) StaticFields.extraArguments ready.1 result actual notTimeout
  have pack:=PackBytesCost.price_bound (extraLength input)
  simp only [BytesCallCost.overhead] at price
  unfold CopyAny.price PackBytes.chunks at *
  omega

end InitECandidate.Solver.Input.CurrentHash.PayloadHash

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.extra_data
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.extra_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.after_extra
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.State.extra_cost
