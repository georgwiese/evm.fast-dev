import InitECandidate.Solver.WitnessRadix.TableMemory

namespace InitECandidate.Solver.WitnessRadix.TableNew
open Flapjack PanSemStateFiniteExact BackingLayout

theorem writes_earlier (memory : WordWrites.Memory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (input : List (BitVec 64 × BitVec 64)) (sites : List Address)
    (cells : input.map Prod.fst = sites.map (address (AllocatedLayout.layout plan)))
    (onlyHeaders : ∀ entry ∈ sites, entry.1 = .header ∧ entry.2 < 72)
    (query : BitVec 64) (earlier : query.toNat < plan.table) : WordWrites.write memory input query = memory query := by
  apply WordWrites.write_away
  rw [cells]
  intro member
  obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp member
  obtain ⟨pool, offset⟩ := entry
  have properties := onlyHeaders (pool, offset) entryMember
  have header : pool = .header := properties.1
  subst pool
  have numeric := congrArg BitVec.toNat same
  change (cell (AllocatedLayout.layout plan) .header offset).toNat = query.toNat at numeric
  rw [header_number plan ready offset properties.2] at numeric
  omega

theorem result_earlier (memory : WordWrites.Memory) (be : Bool) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (query : BitVec 64) (earlier : query.toNat < plan.table) :
    resultMemory memory be plan query = memory query := by
  have beforeHeader : ∀ entry ∈ beforeSites, entry.1 = .header ∧ entry.2 < 72 := by
    intro entry member
    simp only [beforeSites, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have afterHeader : ∀ entry ∈ afterSites, entry.1 = .header ∧ entry.2 < 72 := by
    intro entry member
    simp only [afterSites, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  rw [resultMemory, writes_earlier _ plan ready (afterWrites plan) afterSites (after_cells plan) afterHeader query earlier,
    clear_memory_away _ _ plan ready query (Or.inl (by omega))]
  exact writes_earlier memory plan ready (beforeWrites plan) beforeSites (before_cells plan) beforeHeader query earlier

theorem record_before (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan)
    (offset : Nat) (inside : offset < 16 * plan.count) :
    (cell (AllocatedLayout.layout plan) .records offset).toNat < plan.table := by
  have bounds := AllocatedLayout.extents plan ready .records
  have beforeRecords := ready.recordsBefore
  have number := AllocatedLayout.base_number plan ready .records
  have address := byteAddress_toNat (base (AllocatedLayout.layout plan) .records) offset (by
    rw [number]
    change plan.records + offset < 2 ^ 64
    change 2701131776 ≤ plan.records ∧ plan.records + 16 * plan.count ≤ 33806089496 at bounds
    omega)
  change (byteAddress _ _).toNat < _
  rw [address, number]
  change plan.records + offset < plan.table
  omega

end InitECandidate.Solver.WitnessRadix.TableNew

#print axioms InitECandidate.Solver.WitnessRadix.TableNew.result_earlier
#print axioms InitECandidate.Solver.WitnessRadix.TableNew.record_before
