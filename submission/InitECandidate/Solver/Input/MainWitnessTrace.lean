import InitECandidate.Solver.Input.MainWitnessBody
import InitECandidate.Solver.Input.Witness.DecodedFrame

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The complete literal witness suffix after the real request return,
including SI32, wp/wlen declarations, all guards/lists/stores and decoder
return. Every non-timeout failure is covered; actual normal data survives
all lexical scopes into this very poststate. -/
theorem witness_suffix (input : Guest.InputBlob) (source caller current post : PanSemStateFiniteExact 64 Guest.HostMemory) (counts : Nat → BitVec 64)
    (environment : Environment input source) (actual : RequestCaller input source caller)
    (returned : RequestsReturned input source caller current counts) (layout : RequestLayout input)
    (bounded : input.length % 2^64 ≤ Guest.maxInputBytes)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState current Request.afterRequests = (result,post)) (notTimeout : result ≠ some .timeOut) :
    source.clock-post.clock≤(input.length%2^64)/4+witnessLength input/2+522 ∧
      ((∃ error : BitVec 64,(error=82#64 ∨ error=10#64 ∨ error=11#64 ∨ error=12#64 ∨ error=20#64 ∨ error=21#64 ∨ error=22#64 ∨ error=23#64 ∨ error=70#64) ∧ result=some (.exception (ofString "SszErr") (.val (.word error)))) ∨
       (result=some (.returned (.val (.word (RequestPrefix.cursor input)))) ∧
        Witness.offsetNat input (witnessStart input) 0=12 ∧ 12≤Witness.offsetNat input (witnessStart input) 1 ∧
        Witness.offsetNat input (witnessStart input) 1≤Witness.offsetNat input (witnessStart input) 2 ∧ Witness.offsetNat input (witnessStart input) 2≤witnessLength input ∧
        Witness.Decoded post input inputPointer (witnessArray input) (RequestPrefix.cursor input) (witnessStart input)
          (Witness.offsetNat input (witnessStart input) 0) (Witness.offsetNat input (witnessStart input) 1) (Witness.offsetNat input (witnessStart input) 2) (witnessLength input) (.val (.word (RequestPrefix.cursor input))))) := by
  rcases witness_prefix_trace input source caller current post counts environment actual returned layout bounded result run notTimeout with rejected | normal
  · obtain ⟨same,cost⟩ := rejected
    exact ⟨by omega,Or.inl ⟨82#64,Or.inl rfl,same⟩⟩
  obtain ⟨minimum,inside,next,innerPost,restoreStack,entry,remaining,endpoint,preserved⟩ := normal
  obtain ⟨bodyCost,cost,outcome⟩ := witness_body input source next innerPost counts environment entry bounded minimum inside result remaining notTimeout
  have frame : emptyLocalsHOLFinite post=emptyLocalsHOLFinite innerPost := by rw [endpoint]; exact preserved _
  have clock : post.clock=innerPost.clock := by have h := congrArg PanSemStateFiniteExact.clock frame; exact h
  refine ⟨by rw [clock]; exact cost,?_⟩
  rcases outcome with rejected | normal
  · obtain ⟨error,allowed,same⟩ := rejected
    exact Or.inl ⟨error,Or.inr allowed,same⟩
  · obtain ⟨same,first,middleLower,ordered,lastUpper,decoded⟩ := normal
    have memory : post.memory=innerPost.memory := by have h := congrArg PanSemStateFiniteExact.memory frame; exact h
    have globals : post.globals=innerPost.globals := by have h := congrArg PanSemStateFiniteExact.globals frame; exact h
    have domain : post.memaddrs=innerPost.memaddrs := by have h := congrArg PanSemStateFiniteExact.memaddrs frame; exact h
    have endian : post.be=innerPost.be := by have h := congrArg PanSemStateFiniteExact.be frame; exact h
    exact Or.inr ⟨same,first,middleLower,ordered,lastUpper,Witness.Decoded.of_fields innerPost post _ _ _ _ _ _ _ _ _ _ memory globals domain endian decoded⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.witness_suffix
