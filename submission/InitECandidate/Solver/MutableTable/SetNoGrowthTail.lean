import InitECandidate.Solver.MutableTable.InsertLookup
import InitECandidate.Solver.MutableTable.InsertGeneralCall
import InitECandidate.Solver.MutableTable.SetUpdate

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- Actual setter suffix with its real growth guard proved false. Existing
keys update one value; absent keys execute the whole original raw insertion.
The physical item counter is preserved or incremented, respectively. -/
theorem no_growth_tail (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (kind : KeyHash.Kind) (vals order position count value index : BitVec 64) (bits : Nat) (items : List Nat)
    (data : Insert.GeneralData source table p kind vals order position count bits items)
    (tLocal : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word p.key)))
    (valueLocal : source.locals.lookup (ofString "value") = some (.val (.word value)))
    (iLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (bounded : index.toNat ≤ p.capacity.toNat)
    (countBound : count.toNat ≤ items.length) (room : 2 * items.length + 2 ≤ 2 ^ bits)
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one))
    (enough : Insert.rawPrice kind items.length ≤ source.clock) :
    ∃ paid memory target, paid ≤ Insert.rawPrice kind items.length ∧
      evaluateHOLFiniteState source afterIndex = (some (.returned (.val (.word 0#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - paid} ∧
      memory (table + 24#64) = .word (if index = p.capacity then count + 1#64 else count) := by
  classical
  have capRead := Find.table_read source table 16#64 p.capacity tLocal (data.header.mapped 16 (by simp)) data.header.capacity
  by_cases same : index = p.capacity
  · have skipped : evaluateHOLFiniteState source (.ite presentTest updateBranch .skip) = (none, source) := by
      simp only [eval] at capRead
      simp [evaluateHOLFiniteState_ite, presentTest, evalHOLExact, toExact, localVar, iLocal, capRead, same,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have mapped : ∀ offset ∈ ([16, 24] : List Nat), source.memaddrs (table + BitVec.ofNat 64 offset) := by
      intro offset member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact data.header.mapped 16 (by simp)
      · exact data.countMapped
    have notGrowing := no_growth source table count.toNat (2 ^ bits) items.length countBound room
      (Nat.pow_lt_pow_right (by decide) data.small) tLocal mapped
      (by simpa only [data.capacity] using data.header.capacity)
      (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using data.countCell)
    have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address))
        [localVar "t", localVar "key", localVar "value"] = some (TableCall.values table p.key value) := by
      simp [TableCall.values, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, tLocal, keyLocal, valueLocal]
    obtain ⟨paid, slot, paidBound, inside, inserted, counter⟩ := Insert.general_call source table p kind vals order position count value bits items data
      insertCode [localVar "t", localVar "key", localVar "value"] args enough
    let memory := Insert.generalResultMemory source.memory source.be (KeyHash.keySize kind) p table vals order position slot count value
    let post := {source with memory := memory, clock := source.clock - paid}
    change evaluateHOLFiniteState source insertCall = (none, post) at inserted
    have returned : evaluateHOLFiniteState post Insert.returnZero = (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite post) := by
      simp [Insert.returnZero, evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    refine ⟨paid, memory, emptyLocalsHOLFinite post, paidBound, ?_, rfl, by simpa only [if_pos same] using counter⟩
    rw [afterIndex, StateSteps.next_sequence source source _ _ skipped (Nat.le_refl _),
      afterPresent, StateSteps.next_sequence source source _ _ notGrowing (Nat.le_refl _),
      StateSteps.next_sequence source post insertCall Insert.returnZero inserted (Nat.sub_le _ _)]
    exact returned
  · have unequal : index.toNat ≠ p.capacity.toNat := fun equal => same (BitVec.eq_of_toNat_eq equal)
    have inside : index.toNat < p.capacity.toNat := by omega
    have slotData := data.slots index inside
    let memory := StoreWord.put source.memory (vals + index * 8#64) value
    have run := update_execute source table vals index p.capacity value tLocal iLocal valueLocal
      (data.header.mapped 16 (by simp)) data.header.capacity data.valsMapped data.valsCell slotData.valueMapped same
    refine ⟨0, memory, emptyLocalsHOLFinite {source with memory := memory}, Nat.zero_le _, run, ?_, ?_⟩
    · simp only [Nat.sub_zero, emptyLocalsHOLFinite]
    · simpa only [memory, StoreWord.put, if_neg slotData.awayValue, if_neg same] using data.countCell

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.no_growth_tail
