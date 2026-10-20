import InitECandidate.Solver.Input.MainWitnessGeometry
import InitECandidate.Solver.Input.BytesList.OriginalCode
import InitECandidate.Solver.Input.DecoderRuntimeCode
import InitECandidate.Solver.Input.Witness.BodyNormalPadded

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

/-- All witness runtime code and mapping facts come from main's installed
original code at this actual state, rather than a hypothetical future model. -/
theorem WitnessEntry.runtime (input : Guest.InputBlob) (source entry : PanSemStateFiniteExact 64 Guest.HostMemory) (counts : Nat → BitVec 64) (allowance : Nat)
    (environment : Environment input source) (actual : WitnessEntry input source entry counts allowance) : Witness.Environment entry := by
  have installed : OriginalCode.Installed entry.code := actual.code.symm ▸ environment.code
  exact ⟨actual.domain.trans environment.domain,PersistentAlloc.original_code entry.code installed,original_fail_code entry.code installed,
    by rw [actual.exceptions]; exact environment.shapes .SszErr,
    DecoderRuntime.var_list_code entry.code installed,BytesList.original_code entry.code installed⟩

/-- Complete original normal witness body at main's reached entry. Exact
semantic clock padding removes every sufficient-clock premise; the three
actual record arrays, SI fields and size/count limits refer to the observed
unpadded poststate. No constructor or later EVM outcome is assumed. -/
theorem normal_witness (input : Guest.InputBlob) (source entry post : PanSemStateFiniteExact 64 Guest.HostMemory) (counts : Nat → BitVec 64)
    (environment : Environment input source) (actual : WitnessEntry input source entry counts)
    (bounded : input.length % 2^64 ≤ Guest.maxInputBytes) (minimum : 12 ≤ witnessLength input)
    (inside : witnessStart input + witnessLength input = input.length % 2^64)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState entry Witness.offsetBody = (some (.returned value),post)) :
    Witness.offsetNat input (witnessStart input) 0 = 12 ∧ 12 ≤ Witness.offsetNat input (witnessStart input) 1 ∧
      Witness.offsetNat input (witnessStart input) 1 ≤ Witness.offsetNat input (witnessStart input) 2 ∧ Witness.offsetNat input (witnessStart input) 2 ≤ witnessLength input ∧
      Witness.Decoded post input inputPointer (witnessArray input) (RequestPrefix.cursor input) (witnessStart input)
        (Witness.offsetNat input (witnessStart input) 0) (Witness.offsetNat input (witnessStart input) 1) (Witness.offsetNat input (witnessStart input) 2) (witnessLength input) value ∧
      entry.clock - post.clock ≤ 6 * (input.length % 2^64) + 17 ∧ source.clock - post.clock ≤ (input.length % 2^64) / 4 + 6 * (input.length % 2^64) + 519 ∧ post.clock ≤ entry.clock := by
  have geometry := witness_geometry input bounded actual.transactions
  have installed : OriginalCode.Installed entry.code := actual.code.symm ▸ environment.code
  have offsets : entry.globals.lookup (ofString "ssz_offs") = some (.val (.word 2713715344#64)) := (actual.globals _ (by decide)).trans environment.offsets
  obtain ⟨first,middleLower,ordered,lastUpper,decoded,cost,forward⟩ := Witness.body_normal_any_clock entry post input inputPointer 2713715344#64 (witnessArray input) (RequestPrefix.cursor input) (witnessStart input) (witnessLength input)
    (actual.runtime input source entry counts 502 environment) actual.bytes minimum inside.le actual.pointer actual.length offsets
    (by decide) (by decide) (by decide) (by decide) (by decide) geometry.2.1 geometry.2.2.1 geometry.2.2.2.1 actual.heap
    (original_offsets_code entry.code installed) actual.si geometry.2.2.2.2.1 geometry.2.2.2.2.2.1 geometry.2.2.2.2.2.2.1 geometry.2.2.2.2.2.2.2 value run
  have before := actual.forward
  have prefixCost := actual.cost
  exact ⟨first,middleLower,ordered,lastUpper,decoded,cost,by omega,forward⟩

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.WitnessEntry.runtime
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.normal_witness
