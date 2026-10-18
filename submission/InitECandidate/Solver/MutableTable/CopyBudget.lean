import InitECandidate.Solver.MutableTable.CopyExecution

namespace InitECandidate.Solver.MutableTable.TableCopy
open Flapjack WitnessRadix NaturalLayout

def price (kind : KeyHash.Kind) (capacity : Nat) : Nat :=
  15 + CopyWords.prefixCost (stride kind * capacity) + 3 * CopyWords.prefixCost (8 * capacity) +
    if capacity = 4 then 4 else CopyWords.prefixCost capacity

theorem word_cost (kind : KeyHash.Kind) (old next : Plan) (oldValid : Valid kind old) (nextValid : Valid kind next)
    (pool : Pool) (length : Nat) (multiple : length % 8 = 0) :
    CopyGeneral.cost (cell old pool 0) (cell next pool 0) length = CopyWords.prefixCost length := by
  have aligned := CopyContents.regions_aligned (region kind old pool) (region kind next pool)
    (MemoryRegion.pool_valid kind old oldValid pool) (MemoryRegion.pool_valid kind next nextValid pool)
  rw [region_pointer, region_pointer] at aligned
  rw [CopyGeneral.cost, if_pos aligned, CopyContents.prefix_index_word_multiple length multiple]
  simp only [CopyBytes.suffixCost, Nat.sub_self, Nat.zero_div, Nat.zero_mod, Nat.add_zero]

theorem used_cost (kind : KeyHash.Kind) (old next : Plan) (oldValid : Valid kind old) (nextValid : Valid kind next)
    (shape : old.capacity = 4 ∨ old.capacity % 8 = 0) :
    CopyGeneral.cost (cell old .used 0) (cell next .used 0) old.capacity =
      if old.capacity = 4 then 4 else CopyWords.prefixCost old.capacity := by
  by_cases four : old.capacity = 4
  · have aligned := CopyContents.regions_aligned (region kind old .used) (region kind next .used)
      (MemoryRegion.pool_valid kind old oldValid .used) (MemoryRegion.pool_valid kind next nextValid .used)
    rw [region_pointer, region_pointer] at aligned
    rw [if_pos four, CopyGeneral.cost, if_pos aligned, four]
    rfl
  · rw [if_neg four]
    exact word_cost kind old next oldValid nextValid .used old.capacity (shape.resolve_left four)

/-- Exact source-clock price of the complete original body. Each 32-byte
copy iteration costs one source clock; no byte-per-clock relaxation is used. -/
theorem exact_price (kind : KeyHash.Kind) (old next : Plan) (oldValid : Valid kind old) (nextValid : Valid kind next)
    (shape : old.capacity = 4 ∨ old.capacity % 8 = 0) : walkPrice kind old next pools = price kind old.capacity := by
  have header := word_cost kind old next oldValid nextValid .header 72 (by decide)
  have keys := word_cost kind old next oldValid nextValid .keys (stride kind * old.capacity) (amount_multiple kind old .keys (by decide))
  have values := word_cost kind old next oldValid nextValid .values (8 * old.capacity) (by omega)
  have order := word_cost kind old next oldValid nextValid .order (8 * old.capacity) (by omega)
  have position := word_cost kind old next oldValid nextValid .position (8 * old.capacity) (by omega)
  have used := used_cost kind old next oldValid nextValid shape
  simp only [pools, walkPrice, stagePrice, amount, header, keys, values, order, position, used, price]
  norm_num only [CopyWords.prefixCost, Nat.reduceDiv, Nat.reduceMod]
  omega

theorem price_four (kind : KeyHash.Kind) : price kind 4 + 1 =
    match kind with | .account => 26 | .indexedAccount => 27 | .word => 27 | .storage => 30 | .indexedStorage => 31 := by
  cases kind <;> decide

end InitECandidate.Solver.MutableTable.TableCopy

#print axioms InitECandidate.Solver.MutableTable.TableCopy.word_cost
#print axioms InitECandidate.Solver.MutableTable.TableCopy.used_cost
#print axioms InitECandidate.Solver.MutableTable.TableCopy.exact_price
#print axioms InitECandidate.Solver.MutableTable.TableCopy.price_four
