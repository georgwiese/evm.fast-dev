import InitECandidate.Solver.MutableTable.DeleteModelOwnership
import InitECandidate.Solver.MutableTable.DeleteModelCallValues
import InitECandidate.Solver.GasBudget.WarmKeysInvariant
import InitECandidate.Solver.ClockPaddingFull

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- Actual original deletion caller with no source-clock allowance. The
current owned physical table supplies room/power bounds; actual non-timeout
clock equality removes temporary funding and retains the full ownership post. -/
theorem model_call_normal_values (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (slots : List Nat) (cursor floor : Nat)
    (table : TableState source kind plan slots cursor floor) (environment : GasBudget.WarmKeys.Environment source)
    (query : BitVec 64) (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (deleteCode : source.code.lookup (ofString "htab_del") = some (Find.formals, body, .one))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word (cell plan .header 0)), .val (.word query)])
    (property : BitVec 64 → Prop) (values : Get.OccupiedValuesHave source (cell plan .values 0) (BitVec.ofNat 64 plan.capacity) slots property)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "htab_del") arguments) = (none, target)) :
    ∃ paid memory next flag, paid ≤ modelPrice kind slots.length + 1 ∧ paid ≤ source.clock ∧
      target = modelCallState source paid memory ∧ ModelPost source kind plan slots paid memory target next flag ∧ 2 * next.length ≤ plan.capacity ∧ Get.OccupiedValuesHave target (cell plan .values 0) (BitVec.ofNat 64 plan.capacity) next property := by
  classical
  obtain ⟨bits, power, minimum⟩ := table.power
  obtain ⟨newSmall, _, _⟩ := MemoryModel.growth_shape kind plan table.valid bits power minimum
  have small : bits < 64 := by omega
  have room : slots.length < plan.capacity := by have positive := table.valid.positive; have half := table.half; omega
  let extra := modelPrice kind slots.length + 1
  let padded := {source with clock := source.clock + extra}
  have paddedModel : MemoryModel.Occupied padded kind plan slots := MemoryModel.Occupied.of_fields source padded kind plan slots table.occupied rfl rfl rfl
  have paddedArgs : evalListHOLFinite padded (h := fun address => Classical.propDecidable (padded.memaddrs address)) arguments = some [.val (.word (cell plan .header 0)), .val (.word query)] := by
    change evalListHOLExact (stateAddClock source.toExact extra) arguments = _
    rw [evalListHOLExact_stateAddClock]
    exact args
  obtain ⟨paid, memory, next, flag, bounded, actual, post, half, nextValues⟩ := model_call_values padded kind plan table.valid environment.domain environment.little slots room paddedModel bits small power table.header query queryFits queryMapped
    environment.hashCode environment.copyCode environment.memeqCode environment.findCode deleteCode arguments paddedArgs property values (by change extra ≤ source.clock + extra; omega)
  have lifted := panPropsEvaluateAddClockEq (.call (some (none, none)) (ofString "htab_del") arguments) source none target extra ⟨normal, by intro impossible; cases impossible⟩
  have same := congrArg Prod.snd (lifted.symm.trans actual)
  change {target with clock := target.clock + extra} = modelCallState padded paid memory at same
  have stripped := InitECandidate.Solver.strip_full_clock_padding source target {source with memory := memory} paid extra (by change paid ≤ source.clock + extra; change paid ≤ extra at bounded; omega) same
  have occupied : MemoryModel.Occupied target kind plan next := by
    have paddedOccupied : MemoryModel.Occupied {target with clock := target.clock + extra} kind plan next := by rw [same]; exact post.occupied
    exact MemoryModel.Occupied.of_fields {target with clock := target.clock + extra} target kind plan next paddedOccupied rfl rfl rfl
  have finalValues : Get.OccupiedValuesHave target (cell plan .values 0) (BitVec.ofNat 64 plan.capacity) next property := by
    have paddedValues : Get.OccupiedValuesHave {target with clock:=target.clock+extra} (cell plan .values 0) (BitVec.ofNat 64 plan.capacity) next property := by
      rw [same]
      exact nextValues
    exact paddedValues
  refine ⟨paid, memory, next, flag, bounded, stripped.1, stripped.2, ?_, half table.half,finalValues⟩
  exact ⟨congrArg emptyLocalsHOLFinite stripped.2, post.shape, post.header, occupied, post.footprint⟩

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.model_call_normal_values
