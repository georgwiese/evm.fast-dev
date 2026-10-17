import InitECandidate.Solver.MutableTable.MemoryModelBounds
import InitECandidate.Solver.MutableTable.SetProgram

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original unsigned growth guard reads true at the natural count
threshold. The physical owned extent excludes count arithmetic wrap. -/
theorem growth_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (valid : Valid kind plan) (domain : source.memaddrs = InitE.ordinaryDomain) (count : Nat) (countBound : count ≤ plan.capacity)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 count))
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (threshold : plan.capacity < 2 * count + 2) :
    eval source growthTest = some (.val (.word 1#64)) := by
  have high := valid.upper .values
  change plan.base .values + 8 * plan.capacity ≤ 33806089496 at high
  have countSmall : count + 1 < 2 ^ 64 := by omega
  have twiceSmall : (count + 1) * 2 < 2 ^ 64 := by omega
  have capacitySmall : plan.capacity < 2 ^ 64 := by omega
  have mappedHeader (offset : Nat) (inside : offset < 72) (aligned : offset % 8 = 0) : source.memaddrs (cell plan .header 0 + BitVec.ofNat 64 offset) := by
    rw [domain, constant_cell]
    exact mapped kind plan valid .header offset inside aligned
  have capCell : source.memory (cell plan .header 0 + 16#64) = .word (BitVec.ofNat 64 plan.capacity) := by
    rw [constant_cell]
    exact header 16 _ (by simp [MemoryModel.headerEntries])
  have countCell : source.memory (cell plan .header 0 + 24#64) = .word (BitVec.ofNat 64 count) := by
    rw [constant_cell]
    exact header 24 _ (by simp [MemoryModel.headerEntries])
  have capRead := Find.table_read source _ 16#64 _ tableLocal (mappedHeader 16 (by decide) (by decide)) capCell
  have countRead := Find.table_read source _ 24#64 _ tableLocal (mappedHeader 24 (by decide) (by decide)) countCell
  have sum : BitVec.ofNat 64 count + 1#64 = BitVec.ofNat 64 (count + 1) := by rw [BitVec.ofNat_add]
  have product : BitVec.ofNat 64 (count + 1) * 2#64 = BitVec.ofNat 64 ((count + 1) * 2) := by rw [BitVec.ofNat_mul]
  have comparison : (BitVec.ofNat 64 plan.capacity).toNat < (BitVec.ofNat 64 ((count + 1) * 2)).toNat := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt capacitySmall, Nat.mod_eq_of_lt twiceSmall]
    omega
  change plan.capacity % 18446744073709551616 < ((count + 1) * 2) % 18446744073709551616 at comparison
  simp only [eval] at capRead countRead ⊢
  simp [growthTest, growthExpression, evalHOLExact, evalListHOLExact, toExact, capRead, countRead,
    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, sum, product,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, comparison]

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.growth_read
