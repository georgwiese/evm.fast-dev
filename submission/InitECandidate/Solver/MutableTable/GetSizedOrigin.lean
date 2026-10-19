import InitECandidate.Solver.MutableTable.GetTail32

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Absent results or the actual bounded value-array word loaded by the
original getter. This records physical provenance without key equality. -/
def ValueOrigin (source : PanSemStateFiniteExact 64 Guest.HostMemory) (vals capacity flag value : BitVec 64) : Prop :=
  flag=0#64 ∨ ∃ slot : BitVec 64,slot.toNat<capacity.toNat ∧ source.memory (vals+slot*8#64)=.word value

/-- The original retrieval suffix performs its actual absent/present branch
and mapped value read. This runtime contract needs typed occupied values, not
logical byte-key equality or any hash assumption. -/
theorem sized_tail_origin (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table vals index capacity : BitVec 64)
    (tLocal : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (iLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (capMapped : source.memaddrs (table + 16#64)) (capCell : source.memory (table + 16#64) = .word capacity)
    (valsMapped : source.memaddrs (table + 40#64)) (valsCell : source.memory (table + 40#64) = .word vals)
    (values : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      ∃ value, source.memaddrs (vals + slot * 8#64) ∧ source.memory (vals + slot * 8#64) = .word value)
    (bounded : index.toNat ≤ capacity.toNat) :
    ∃ flag value, (flag = 0#64 ∨ flag = 1#64) ∧ ValueOrigin source vals capacity flag value ∧
      evaluateHOLFiniteState source afterIndex = (some (.returned (pair flag value)), emptyLocalsHOLFinite source) := by
  classical
  have capRead := Find.table_read source table 16#64 capacity tLocal capMapped capCell
  simp only [eval] at capRead
  by_cases same : index = capacity
  · have stopped : evaluateHOLFiniteState source (.ite condition absent .skip) =
        (some (.returned (pair 0#64 0#64)), emptyLocalsHOLFinite source) := by
      simp [condition, evaluateHOLFiniteState_ite, evalHOLExact, toExact, localVar, iLocal, capRead, same,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, absent, pair, evaluateHOLFiniteState_return, evalListHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    refine ⟨0#64, 0#64, Or.inl rfl, Or.inl rfl, ?_⟩
    rw [afterIndex, WitnessRadix.StateSteps.stopped_sequence source (emptyLocalsHOLFinite source) _ _ _ stopped (Nat.le_refl _)]
  · have unequal : index.toNat ≠ capacity.toNat := fun equality => same (BitVec.eq_of_toNat_eq equality)
    have inside : index.toNat < capacity.toNat := by omega
    have skipped : evaluateHOLFiniteState source (.ite condition absent .skip) = (none, source) := by
      simp [condition, evaluateHOLFiniteState_ite, evalHOLExact, toExact, localVar, iLocal, capRead, same,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have valsRead := Find.table_read source table 40#64 vals tLocal valsMapped valsCell
    obtain ⟨value, valueMapped, valueCell⟩ := values index inside
    have read : eval source valueExpression = some (.val (.word value)) := by
      simp only [eval] at valsRead ⊢
      simp [valueExpression, evalHOLExact, evalListHOLExact, toExact, localVar, iLocal, valsRead, valueIsWord, valueWord, wordOpHOL, wordOp,
        panOpHOL, memLoadHOLExact, isWfShapeExactHOL, valueMapped, valueCell]
    have returned : evaluateHOLFiniteState source present = (some (.returned (pair 1#64 value)), emptyLocalsHOLFinite source) := by
      simp only [eval] at read
      simp [present, pair, evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, read, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    refine ⟨1#64, value, Or.inr rfl, Or.inr ⟨index,inside,valueCell⟩, ?_⟩
    rw [afterIndex, WitnessRadix.StateSteps.next_sequence source source _ _ skipped (Nat.le_refl _)]
    exact returned

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.sized_tail_origin
