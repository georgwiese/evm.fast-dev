import InitECandidate.Solver.Input.MainWitnessTrace

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Physical final witness data with the actual original ordered slices. -/
def WitnessDecoded (input : Guest.InputBlob) (current : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  Witness.offsetNat input (witnessStart input) 0=12 ∧ 12≤Witness.offsetNat input (witnessStart input) 1 ∧
  Witness.offsetNat input (witnessStart input) 1≤Witness.offsetNat input (witnessStart input) 2 ∧ Witness.offsetNat input (witnessStart input) 2≤witnessLength input ∧
  Witness.Decoded current input inputPointer (witnessArray input) (RequestPrefix.cursor input) (witnessStart input)
    (Witness.offsetNat input (witnessStart input) 0) (Witness.offsetNat input (witnessStart input) 1) (Witness.offsetNat input (witnessStart input) 2) (witnessLength input) (.val (.word (RequestPrefix.cursor input)))

theorem WitnessDecoded.of_frame (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite source) (actual : WitnessDecoded input source) : WitnessDecoded input target := by
  obtain ⟨first,lower,ordered,upper,decoded⟩ := actual
  have memory : target.memory=source.memory := by have h := congrArg PanSemStateFiniteExact.memory frame; exact h
  have globals : target.globals=source.globals := by have h := congrArg PanSemStateFiniteExact.globals frame; exact h
  have domain : target.memaddrs=source.memaddrs := by have h := congrArg PanSemStateFiniteExact.memaddrs frame; exact h
  have endian : target.be=source.be := by have h := congrArg PanSemStateFiniteExact.be frame; exact h
  exact ⟨first,lower,ordered,upper,Witness.Decoded.of_fields source target _ _ _ _ _ _ _ _ _ _ memory globals domain endian decoded⟩

/-- Both complete original request/witness decoders, from the actual request
caller to the original decoder return. Rejections include all real helper
failures and the final physical records survive the request's rq scope. -/
theorem requests_witness_trace (input : Guest.InputBlob) (source caller post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : Environment input source) (actual : RequestCaller input source caller) (layout : RequestLayout input)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState caller Request.requestsCall=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤(input.length%2^64)/4+witnessLength input/2+522 ∧
      ((∃ error : BitVec 64,result=some (.exception (ofString "SszErr") (.val (.word error)))) ∨
       (result=some (.returned (.val (.word (RequestPrefix.cursor input)))) ∧ WitnessDecoded input post)) := by
  rcases requests_return_trace input source caller post environment actual layout bounded result run notTimeout with rejected | normal
  · obtain ⟨error,allowed,same,cost,aggregate⟩ := rejected
    exact ⟨by omega,Or.inl ⟨error,same⟩⟩
  obtain ⟨current,final,counts,returned,remaining,endpoint⟩ := normal
  obtain ⟨cost,outcome⟩ := witness_suffix input source caller current final counts environment actual returned layout bounded result remaining notTimeout
  have frame : emptyLocalsHOLFinite post=emptyLocalsHOLFinite final := by rw [endpoint]; rfl
  have clock : post.clock=final.clock := by have h := congrArg PanSemStateFiniteExact.clock frame; exact h
  refine ⟨by rw [clock]; exact cost,?_⟩
  rcases outcome with rejected | normal
  · obtain ⟨error,allowed,same⟩ := rejected
    exact Or.inl ⟨error,same⟩
  · exact Or.inr ⟨normal.1,WitnessDecoded.of_frame input final post frame normal.2⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.WitnessDecoded.of_frame
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.requests_witness_trace
