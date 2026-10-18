import InitECandidate.Solver.GasBudget.JournalZone
import Mathlib.Data.List.FinRange

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack MutableTable

theorem entry_number (base cap index : Nat) (field : Fin 4)
    (valid : MemoryRegion.Valid ⟨base, 32 * cap⟩) (inside : index < cap) :
    (entryAddress base index field).toNat = base + 32 * index + 8 * field.val := by
  have upper := valid.upper
  change base + 32 * cap ≤ 33806089496 at upper
  have fieldBound := field.isLt
  rw [entryAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- Distinct full journal words cannot alias, including at record boundaries. -/
theorem entry_injective (base cap first second : Nat) (left right : Fin 4)
    (valid : MemoryRegion.Valid ⟨base, 32 * cap⟩) (firstInside : first < cap) (secondInside : second < cap)
    (same : entryAddress base first left = entryAddress base second right) : first = second ∧ left = right := by
  have numeric := congrArg BitVec.toNat same
  rw [entry_number base cap first left valid firstInside, entry_number base cap second right valid secondInside] at numeric
  have leftBound := left.isLt
  have rightBound := right.isLt
  refine ⟨by omega, ?_⟩
  apply Fin.ext
  omega

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.entry_number
#print axioms InitECandidate.Solver.GasBudget.Journal.entry_injective
