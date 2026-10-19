import InitECandidate.Solver.MutableTable.GetGeneralOrigin
import InitECandidate.Solver.MutableTable.TableState
import InitECandidate.Solver.MutableTable.MemoryModelEntry
import InitECandidate.Solver.GasBudget.WarmKeysInvariant

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Current physical table ownership supplies every original getter read,
including arbitrary stored value words and all collision probes. -/
theorem model_execute_origin (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (cursor floor : Nat) (table : TableState source kind plan slots cursor floor)
    (environment : GasBudget.WarmKeys.Environment source) (query : BitVec 64)
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (enough : (Find.generalProbePrice kind * slots.length + (KeyHash.hashPrice kind + 1)) ≤ source.clock) :
    ∃ paid flag value target, paid ≤ (Find.generalProbePrice kind * slots.length + (KeyHash.hashPrice kind + 1)) ∧ (flag = 0#64 ∨ flag = 1#64) ∧ ValueOrigin source (cell plan .values 0) (BitVec.ofNat 64 plan.capacity) flag value ∧
      evaluateHOLFiniteState source body = (some (.returned (pair flag value)), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - paid} := by
  obtain ⟨bits, power, minimum⟩ := table.power
  obtain ⟨newSmall, _, _⟩ := MemoryModel.growth_shape kind plan table.valid bits power minimum
  have small : bits < 64 := by omega
  have room : slots.length < plan.capacity := by have positive := table.valid.positive; have half := table.half; omega
  let p := parameters kind plan query
  have data := MemoryModel.runtime_data source kind plan table.valid environment.domain query slots room table.header table.occupied bits small power queryFits queryMapped
    environment.little environment.hashCode environment.copyCode
  have capNumber : p.capacity.toNat = 2 ^ bits := by
    rw [data.capacity, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) small)]
  have inside (i : Nat) (bounded : i < 2 ^ bits) : (BitVec.ofNat 64 i).toNat < p.capacity.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans bounded (Nat.pow_lt_pow_right (by decide) small)), capNumber]
    exact bounded
  have values (slot : BitVec 64) (bounded : slot.toNat < p.capacity.toNat) :
      ∃ value, source.memaddrs (cell plan .values 0 + slot * 8#64) ∧ source.memory (cell plan .values 0 + slot * 8#64) = .word value := by
    have mapped := (data.slots slot bounded).valueMapped
    cases source.memory (cell plan .values 0 + slot * 8#64) with
    | word value => exact ⟨value, mapped, rfl⟩
  exact general_get_origin source (cell plan .header 0) p kind
    (Find.HeaderData.with_locals source source _ p data.header rfl rfl tableLocal keyLocal) data.keyLength bits small data.capacity slots data.room data.binary data.covered
    (fun i bounded => (data.slots _ (inside i bounded)).fits) (fun i bounded => (data.slots _ (inside i bounded)).mapped)
    queryFits queryMapped environment.hashCode environment.memeqCode environment.findCode
    (cell plan .values 0) data.valsMapped data.valsCell values environment.little enough

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.model_execute_origin
