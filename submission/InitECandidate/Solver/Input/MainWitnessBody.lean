import InitECandidate.Solver.Input.MainWitnessNormal
import InitECandidate.Solver.Input.Witness.BodyTrace

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Complete original witness body at main's reached state, including all
parser failures. Its actual offset/list cost uses the shared witness slice;
normal physical records come from the same observed unpadded execution. -/
theorem witness_body_frame (input : Guest.InputBlob) (source entry post : PanSemStateFiniteExact 64 Guest.HostMemory) (counts : Nat → BitVec 64)
    (environment : Environment input source) (actual : WitnessEntry input source entry counts)
    (bounded : input.length % 2^64 ≤ Guest.maxInputBytes) (minimum : 12 ≤ witnessLength input)
    (inside : witnessStart input + witnessLength input = input.length % 2^64)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState entry Witness.offsetBody=(result,post)) (notTimeout : result≠some .timeOut) :
    entry.clock-post.clock≤witnessLength input/2+20 ∧ source.clock-post.clock≤(input.length%2^64)/4+witnessLength input/2+522 ∧
      ((∃ error : BitVec 64,(error=10#64 ∨ error=11#64 ∨ error=12#64 ∨ error=20#64 ∨ error=21#64 ∨ error=22#64 ∨ error=23#64 ∨ error=70#64) ∧ result=some (.exception (ofString "SszErr") (.val (.word error)))) ∨
       (result=some (.returned (.val (.word (RequestPrefix.cursor input)))) ∧
        Witness.offsetNat input (witnessStart input) 0=12 ∧ 12≤Witness.offsetNat input (witnessStart input) 1 ∧
        Witness.offsetNat input (witnessStart input) 1≤Witness.offsetNat input (witnessStart input) 2 ∧ Witness.offsetNat input (witnessStart input) 2≤witnessLength input ∧
        Witness.Decoded post input inputPointer (witnessArray input) (RequestPrefix.cursor input) (witnessStart input)
          (Witness.offsetNat input (witnessStart input) 0) (Witness.offsetNat input (witnessStart input) 1) (Witness.offsetNat input (witnessStart input) 2) (witnessLength input) (.val (.word (RequestPrefix.cursor input))) ∧
        (∀ query,inputPointer.toNat≤query.toNat → query.toNat<(witnessArray input).toNat →
          query≠byteAddress (RequestPrefix.cursor input) 40 → query≠byteAddress (RequestPrefix.cursor input) 48 → query≠byteAddress (RequestPrefix.cursor input) 56 → query≠byteAddress (RequestPrefix.cursor input) 64 → query≠byteAddress (RequestPrefix.cursor input) 72 → query≠byteAddress (RequestPrefix.cursor input) 80 → post.memory query=entry.memory query) ∧ InitializerAllocations.context post=InitializerAllocations.context entry)) := by
  have geometry := witness_geometry input bounded actual.transactions
  have installed : OriginalCode.Installed entry.code := actual.code.symm ▸ environment.code
  have offsets : entry.globals.lookup (ofString "ssz_offs")=some (.val (.word 2713715344#64)) := (actual.globals _ (by decide)).trans environment.offsets
  obtain ⟨cost,outcome⟩ := Witness.body_trace_frame entry post input inputPointer 2713715344#64 (witnessArray input) (RequestPrefix.cursor input) (witnessStart input) (witnessLength input)
    (actual.runtime input source entry counts 502 environment) actual.bytes minimum inside.le actual.pointer actual.length offsets
    (by decide) (by decide) (by decide) (by decide) (by decide) geometry.2.1 geometry.2.2.1 geometry.2.2.2.1 actual.heap
    (original_offsets_code entry.code installed) actual.si geometry.2.2.2.2.1 geometry.2.2.2.2.2.1 geometry.2.2.2.2.2.2.1 geometry.2.2.2.2.2.2.2 result run notTimeout
  have postForward := evaluateHOLFiniteState_clock_le entry Witness.offsetBody
  rw [run] at postForward
  change post.clock≤entry.clock at postForward
  have before := actual.forward
  have prefixCost := actual.cost
  refine ⟨cost,by omega,?_⟩
  rcases outcome with rejected | normal
  · exact Or.inl rejected
  · have actualRun : evaluateHOLFiniteState entry Witness.offsetBody=(some (.returned (.val (.word (RequestPrefix.cursor input)))),post) := by rw [run,normal.1]
    obtain ⟨first,middleLower,ordered,lastUpper,decoded,bodyCost,aggregate,forward⟩ := normal_witness input source entry post counts environment actual bounded minimum inside _ actualRun
    refine Or.inr ⟨normal.1,first,middleLower,ordered,lastUpper,decoded,?_,normal.2.2⟩
    intro query lower before nodePtr nodeCount codePtr codeCount headerPtr headerCount
    apply normal.2.1 query before _ nodePtr nodeCount codePtr codeCount headerPtr headerCount
    right
    change 2713731432≤query.toNat at lower
    change 2713715344+24≤query.toNat
    omega


/-- Bound and physical-data projection of the stronger real memory frame. -/
theorem witness_body (input : Guest.InputBlob) (source entry post : PanSemStateFiniteExact 64 Guest.HostMemory) (counts : Nat → BitVec 64)
    (environment : Environment input source) (actual : WitnessEntry input source entry counts)
    (bounded : input.length % 2^64 ≤ Guest.maxInputBytes) (minimum : 12 ≤ witnessLength input)
    (inside : witnessStart input + witnessLength input = input.length % 2^64)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState entry Witness.offsetBody=(result,post)) (notTimeout : result≠some .timeOut) :
    entry.clock-post.clock≤witnessLength input/2+20 ∧ source.clock-post.clock≤(input.length%2^64)/4+witnessLength input/2+522 ∧
      ((∃ error : BitVec 64,(error=10#64 ∨ error=11#64 ∨ error=12#64 ∨ error=20#64 ∨ error=21#64 ∨ error=22#64 ∨ error=23#64 ∨ error=70#64) ∧ result=some (.exception (ofString "SszErr") (.val (.word error)))) ∨
       (result=some (.returned (.val (.word (RequestPrefix.cursor input)))) ∧
        Witness.offsetNat input (witnessStart input) 0=12 ∧ 12≤Witness.offsetNat input (witnessStart input) 1 ∧
        Witness.offsetNat input (witnessStart input) 1≤Witness.offsetNat input (witnessStart input) 2 ∧ Witness.offsetNat input (witnessStart input) 2≤witnessLength input ∧
        Witness.Decoded post input inputPointer (witnessArray input) (RequestPrefix.cursor input) (witnessStart input)
          (Witness.offsetNat input (witnessStart input) 0) (Witness.offsetNat input (witnessStart input) 1) (Witness.offsetNat input (witnessStart input) 2) (witnessLength input) (.val (.word (RequestPrefix.cursor input))))) := by
  obtain ⟨cost,aggregate,outcome⟩ := witness_body_frame input source entry post counts environment actual bounded minimum inside result run notTimeout
  refine ⟨cost,aggregate,?_⟩
  rcases outcome with rejected | normal
  · exact Or.inl rejected
  · obtain ⟨same,first,lower,ordered,upper,decoded,frame⟩ := normal
    exact Or.inr ⟨same,first,lower,ordered,upper,decoded⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.witness_body

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.witness_body_frame
