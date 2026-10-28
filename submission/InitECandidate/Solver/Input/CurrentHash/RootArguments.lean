import InitECandidate.Solver.Input.CurrentHash.RootState

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def headerCount (input : Guest.InputBlob) := (Guest.GasLimit.le32 input 58-Guest.GasLimit.le32 input 22)/32
def headerPointer (input : Guest.InputBlob) (blob : BitVec 64) := blob+18#64+Request.requestWords input 1

def Step.values (step : Step) (input : Guest.InputBlob) (blob record rq ch : BitVec 64) : List (ValueHOL 64) := match step with
  | .payload=>FixedRecord.scalarValues record ch
  | .headers=>PListCost.values (headerPointer input blob) (BitVec.ofNat 64 (headerCount input)) (ch+32#64) (headerCount input)
  | .header=>CopyGeneral.values (ch+64#64) (blob+18#64+8#64) 32
  | .requests=>RequestsHash.values rq (ch+96#64)

theorem State.output_read {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob si record rq root array ch cursor : BitVec 64} {length start size : Nat}
    (state : State input source blob si record rq root array ch cursor length start size) (offset : Nat) :
    eval source (outputExpression offset)=some (.val (.word (ch+BitVec.ofNat 64 offset))) := by
  have read : eval source (localVar "ch")=some (.val (.word ch)) := by simpa [eval,evalHOLExact,toExact,localVar] using state.chunks
  exact Scalar.plus_read source _ ch offset read

/-- Literal current root-call arguments come from the same physical SI cells
and allocated chunks, including the actual repeated list count argument. -/
theorem State.arguments_read {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob si record rq root array ch cursor : BitVec 64} {length start size : Nat}
    (state : State input source blob si record rq root array ch cursor length start size) (step : Step) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) step.arguments=some (step.values input blob record rq ch) := by
  have plRead := state.data.si_load 0 (by decide) (by decide) record (by simpa only [BitVec.add_zero] using state.data.payloadCell)
  have pointerRead := state.data.si_load 8 (by decide) (by decide) (headerPointer input blob) state.data.hashPointer
  have countRead := state.data.si_load 16 (by decide) (by decide) (BitVec.ofNat 64 (headerCount input)) state.data.hashCount
  have headerRead := state.data.si_load 24 (by decide) (by decide) (blob+18#64+8#64) state.data.header
  have requestRead := state.data.si_load 32 (by decide) (by decide) rq state.data.requests
  change eval source (field 0)=some (.val (.word record)) at plRead
  change eval source (field 8)=some (.val (.word (headerPointer input blob))) at pointerRead
  change eval source (field 16)=some (.val (.word (BitVec.ofNat 64 (headerCount input)))) at countRead
  change eval source (field 24)=some (.val (.word (blob+18#64+8#64))) at headerRead
  change eval source (field 32)=some (.val (.word rq)) at requestRead
  have output32 := state.output_read 32
  have output64 := state.output_read 64
  have output96 := state.output_read 96
  simp only [eval] at plRead pointerRead countRead headerRead requestRead output32 output64 output96
  cases step <;> simp only [Step.arguments,Step.values,evalListHOLFinite,evalListHOLExact,plRead,pointerRead,countRead,headerRead,requestRead,output32,output64,output96,
    PListCost.values,FixedRecord.scalarValues,CopyGeneral.values,RequestsHash.values,evalHOLExact,localVar,toExact,state.chunks]

theorem State.si_before_chunks {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob si record rq root array ch cursor : BitVec 64} {length start size : Nat}
    (state : State input source blob si record rq root array ch cursor length start size) (offset : Nat) (inside : offset<96) :
    (si+BitVec.ofNat 64 offset).toNat<ch.toNat := by
  have number : (si+BitVec.ofNat 64 offset).toNat=si.toNat+offset := byteAddress_toNat si offset (by have h:=state.data.siArena.upper; omega)
  rw [number]
  have a:=state.data.payloadAfterSI; have b:=state.data.rootAfter; have c:=state.chunksAfter
  omega

end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.output_read
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.arguments_read
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.si_before_chunks
