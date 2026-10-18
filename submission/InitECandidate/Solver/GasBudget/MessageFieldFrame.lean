import InitECandidate.Solver.Input.StoreBoundedNormal
import InitECandidate.Solver.MutableTable.MemoryRegion

namespace InitECandidate.Solver.GasBudget.MessageField
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix MutableTable

def store (offset : Nat) (expression : ExpHOL 64) : ProgHOL 64 := .store (addConst (localVar "m") (BitVec.ofNat 64 offset)) expression

theorem field_number (start offset : Nat) (region : MemoryRegion.Valid ⟨start, 176⟩) (inside : offset ≤ 176) :
    (BitVec.ofNat 64 start + BitVec.ofNat 64 offset).toNat = start + offset := by
  rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have upper := region.upper; change start + 176 ≤ 33806089496 at upper; omega)]

/-- Actual stores to one bounded field of the freshly owned message retain
earlier/later objects and all message words outside that field. -/
theorem normal_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (start offset width : Nat) (expression : ExpHOL 64)
    (region : MemoryRegion.Valid ⟨start, 176⟩) (fits : offset + 8 * width ≤ 176)
    (messageLocal : source.locals.lookup (ofString "m") = some (.val (.word (BitVec.ofNat 64 start))))
    (bounded : ∀ value, eval source expression = some value → (flattenHOL value).length ≤ width)
    (normal : evaluateHOLFiniteState source (store offset expression) = (none, target)) :
    target = {source with memory := target.memory} ∧
      (∀ query : BitVec 64, query.toNat < start ∨ start + 176 ≤ query.toNat → target.memory query = source.memory query) ∧
      ∀ field < 176, (field < offset ∨ offset + 8 * width ≤ field) →
        target.memory (BitVec.ofNat 64 start + BitVec.ofNat 64 field) = source.memory (BitVec.ofNat 64 start + BitVec.ofNat 64 field) := by
  have addressRead : eval source (addConst (localVar "m") (BitVec.ofNat 64 offset)) = some (.val (.word (BitVec.ofNat 64 start + BitVec.ofNat 64 offset))) := by
    simp [eval, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, messageLocal, valueIsWord, valueWord, wordOpHOL, wordOp]
  obtain ⟨frame, preserved⟩ := Input.store_bounded_normal source target _ expression _ width addressRead bounded normal
  have number (index : Nat) (inside : index < width) :
      (BitVec.ofNat 64 start + BitVec.ofNat 64 offset + BitVec.ofNat 64 (8 * index)).toNat = start + offset + 8 * index := by
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have upper := region.upper; change start + 176 ≤ 33806089496 at upper; omega)]
  refine ⟨frame, ?_, ?_⟩
  · intro query outside
    apply preserved query
    intro index inside same
    have numeric := congrArg BitVec.toNat same
    rw [number index inside] at numeric
    omega
  · intro field inside away
    apply preserved _
    intro index insideIndex same
    have numeric := congrArg BitVec.toNat same
    rw [field_number start field region (by omega), number index insideIndex] at numeric
    omega

end InitECandidate.Solver.GasBudget.MessageField

#print axioms InitECandidate.Solver.GasBudget.MessageField.field_number
#print axioms InitECandidate.Solver.GasBudget.MessageField.normal_frame
