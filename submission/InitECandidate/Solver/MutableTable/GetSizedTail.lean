import InitECandidate.Solver.MutableTable.GetSizedOrigin
import InitECandidate.Solver.MutableTable.GetTail32

namespace InitECandidate.Solver.MutableTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original retrieval suffix performs its actual absent/present branch
and mapped value read. This runtime contract needs typed occupied values, not
logical byte-key equality or any hash assumption. -/
theorem sized_tail (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table vals index capacity : BitVec 64)
    (tLocal : source.locals.lookup (ofString "t") = some (.val (.word table)))
    (iLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (capMapped : source.memaddrs (table + 16#64)) (capCell : source.memory (table + 16#64) = .word capacity)
    (valsMapped : source.memaddrs (table + 40#64)) (valsCell : source.memory (table + 40#64) = .word vals)
    (values : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      ∃ value, source.memaddrs (vals + slot * 8#64) ∧ source.memory (vals + slot * 8#64) = .word value)
    (bounded : index.toNat ≤ capacity.toNat) :
    ∃ flag value, (flag = 0#64 ∨ flag = 1#64) ∧
      evaluateHOLFiniteState source afterIndex = (some (.returned (pair flag value)), emptyLocalsHOLFinite source) := by
  obtain ⟨flag,value,binary,origin,run⟩ := sized_tail_origin source table vals index capacity tLocal iLocal capMapped capCell valsMapped valsCell values bounded
  exact ⟨flag,value,binary,run⟩

end InitECandidate.Solver.MutableTable.Get

#print axioms InitECandidate.Solver.MutableTable.Get.sized_tail
