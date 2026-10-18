import InitECandidate.Solver.MutableTable.CopyFrames

namespace InitECandidate.Solver.MutableTable.TableCopy
open Flapjack WitnessRadix NaturalLayout

theorem amount_eq_size (kind : KeyHash.Kind) (plan : Plan) (pool : Pool) (notUsed : pool ≠ .used) :
    amount kind plan.capacity pool = size kind plan pool := by
  cases pool <;> first | rfl | exact False.elim (notUsed rfl)

theorem same_sizes (kind : KeyHash.Kind) (old next : Plan) (sameCapacity : next.capacity = old.capacity) (pool : Pool) :
    size kind next pool = size kind old pool := by cases pool <;> simp only [size, sameCapacity]

theorem stage_word_at (input : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (old next : Plan)
    (oldValid : Valid kind old) (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity)
    (earlier : ∀ first second, old.base first + size kind old first ≤ next.base second)
    (pool : Pool) (notUsed : pool ≠ .used) (query : Nat) (inside : query < size kind old pool) (aligned : query % 8 = 0) :
    stageMemory input be kind old next pool (cell next pool query) = input (cell old pool query) := by
  have copied : CopyGeneral.resultMemory input be (cell old pool 0) (cell next pool 0) (amount kind old.capacity pool)
      (cell next pool query) = input (cell old pool query) := by
    have actual := CopyContents.word_at input be (region kind old pool) (region kind next pool)
      (MemoryRegion.pool_valid kind old oldValid pool) (MemoryRegion.pool_valid kind next nextValid pool)
      (Or.inl (earlier pool pool)) (amount kind old.capacity pool) (amount_room kind old pool)
      (by change amount kind old.capacity pool ≤ size kind next pool; rw [same_sizes kind old next sameCapacity]; exact amount_room kind old pool)
      (amount_multiple kind old pool notUsed) query (by rw [amount_eq_size kind old pool notUsed]; exact inside) aligned
    simpa only [region_pointer, offset_cell] using actual
  unfold stageMemory
  split
  · exact copied
  · rename_i notHeader
    have fieldInside : headerOffset pool < size kind next .header := by cases pool <;> norm_num [headerOffset, size]
    rw [StoreWord.put, if_neg (separate kind next nextValid pool .header notHeader query _ (by rw [same_sizes kind old next sameCapacity]; exact inside) fieldInside)]
    exact copied

theorem stage_used_at (input : WordWrites.Memory) (kind : KeyHash.Kind) (old next : Plan)
    (oldValid : Valid kind old) (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity)
    (earlier : ∀ first second, old.base first + size kind old first ≤ next.base second)
    (shape : old.capacity = 4 ∨ old.capacity % 8 = 0) (query : Nat) (inside : query < old.capacity) :
    CopyContents.byte (stageMemory input false kind old next .used) (cell next .used query) = CopyContents.byte input (cell old .used query) := by
  have copied : CopyContents.byte (CopyGeneral.resultMemory input false (cell old .used 0) (cell next .used 0) old.capacity)
      (cell next .used query) = CopyContents.byte input (cell old .used query) := by
    have actual := CopyContents.used_bytes_at input (region kind old .used) (region kind next .used)
      (MemoryRegion.pool_valid kind old oldValid .used) (MemoryRegion.pool_valid kind next nextValid .used)
      (Or.inl (earlier .used .used)) old.capacity (amount_room kind old .used)
      (by change old.capacity ≤ size kind next .used; rw [same_sizes kind old next sameCapacity]; exact amount_room kind old .used) shape query inside
    simpa only [region_pointer, offset_cell] using actual
  have usedInside : query < size kind next .used := by rw [same_sizes kind old next sameCapacity]; exact used_offset_inside kind old query inside
  have away : panByteAlignHOL (width := 64) (cell next .used query) ≠ cell next .header 48 := by
    rw [byte_cell kind next nextValid .used query usedInside]
    exact separate kind next nextValid .used .header (by decide) _ 48 (by omega) (by change 48 < 72; decide)
  simp only [stageMemory, amount, headerOffset, reduceCtorEq, if_false, CopyContents.byte, StoreWord.put, if_neg away]
  exact copied

/-- Other previously copied data pools survive a later stage, including
their unused padding and byte backing words. -/
theorem stage_other_data (input : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (old next : Plan)
    (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity)
    (pool other : Pool) (different : other ≠ pool) (notHeader : other ≠ .header)
    (query : Nat) (inside : query < size kind next other) :
    stageMemory input be kind old next pool (cell next other query) = input (cell next other query) := by
  have fits : amount kind old.capacity pool ≤ size kind next pool := by rw [← sameCapacity]; exact amount_room kind next pool
  have away : CopyGeneral.Away (cell next pool 0) (cell next other query) (amount kind old.capacity pool) := by
    rw [← region_pointer kind next pool]
    apply MemoryRegion.copy_away _ (MemoryRegion.pool_valid kind next nextValid pool) _ fits
    rw [number kind next nextValid other query inside]
    have apart := nextValid.disjoint other pool different
    change next.base other + query < next.base pool ∨ next.base pool + size kind next pool ≤ next.base other + query
    omega
  have copied := CopyGeneral.resultMemory_away input be (cell old pool 0) (cell next pool 0) (cell next other query) (amount kind old.capacity pool) away
  unfold stageMemory
  split
  · exact copied
  · have fieldInside : headerOffset pool < size kind next .header := by cases pool <;> norm_num [headerOffset, size]
    rw [StoreWord.put, if_neg (separate kind next nextValid other .header notHeader query _ inside fieldInside)]
    exact copied

theorem stage_header_at (input : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (old next : Plan)
    (nextValid : Valid kind next) (sameCapacity : next.capacity = old.capacity) (pool : Pool) (notHeader : pool ≠ .header)
    (query : Nat) (inside : query < 72) :
    stageMemory input be kind old next pool (cell next .header query) =
      if query = headerOffset pool then .word (cell next pool 0) else input (cell next .header query) := by
  have fits : amount kind old.capacity pool ≤ size kind next pool := by rw [← sameCapacity]; exact amount_room kind next pool
  have away : CopyGeneral.Away (cell next pool 0) (cell next .header query) (amount kind old.capacity pool) := by
    rw [← region_pointer kind next pool]
    apply MemoryRegion.copy_away _ (MemoryRegion.pool_valid kind next nextValid pool) _ fits
    rw [number kind next nextValid .header query inside]
    have apart := nextValid.disjoint .header pool (Ne.symm notHeader)
    change next.base .header + query < next.base pool ∨ next.base pool + size kind next pool ≤ next.base .header + query
    change next.base .header + 72 ≤ next.base pool ∨ next.base pool + size kind next pool ≤ next.base .header at apart
    omega
  have copied := CopyGeneral.resultMemory_away input be (cell old pool 0) (cell next pool 0) (cell next .header query) (amount kind old.capacity pool) away
  rw [stageMemory, if_neg notHeader, StoreWord.put]
  by_cases equal : query = headerOffset pool
  · rw [equal, if_pos rfl, if_pos rfl]
  · have fieldInside : headerOffset pool < size kind next .header := by cases pool <;> norm_num [headerOffset, size]
    rw [if_neg (cell_injective kind next nextValid .header query _ inside fieldInside equal), if_neg equal]
    exact copied

end InitECandidate.Solver.MutableTable.TableCopy

#print axioms InitECandidate.Solver.MutableTable.TableCopy.amount_eq_size
#print axioms InitECandidate.Solver.MutableTable.TableCopy.same_sizes
#print axioms InitECandidate.Solver.MutableTable.TableCopy.stage_word_at
#print axioms InitECandidate.Solver.MutableTable.TableCopy.stage_used_at
#print axioms InitECandidate.Solver.MutableTable.TableCopy.stage_other_data
#print axioms InitECandidate.Solver.MutableTable.TableCopy.stage_header_at
