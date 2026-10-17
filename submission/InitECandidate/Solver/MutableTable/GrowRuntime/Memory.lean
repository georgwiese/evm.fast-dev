import InitECandidate.Solver.MutableTable.TableRuntime.Cells
import InitECandidate.Solver.MutableTable.ZeroBytes
import InitECandidate.Solver.MutableTable.MemoryModel

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

def resetSites : List Nat := [16, 32, 40, 48, 56, 64, 24]
def resetWrites (plan : Plan) : List (BitVec 64 × BitVec 64) :=
  [(cell plan .header 16, BitVec.ofNat 64 plan.capacity), (cell plan .header 32, cell plan .keys 0),
   (cell plan .header 40, cell plan .values 0), (cell plan .header 48, cell plan .used 0),
   (cell plan .header 56, cell plan .order 0), (cell plan .header 64, cell plan .position 0),
   (cell plan .header 24, 0#64)]
/-- Exact clear followed by the original growth routine's seven header
stores. Later execution lemmas must establish this memory from actual calls. -/
def resetMemory (memory : WordWrites.Memory) (plan : Plan) : WordWrites.Memory :=
  WordWrites.write (Zero.finalMemory memory (cell plan .used 0) plan.capacity) (resetWrites plan)

theorem reset_cells (plan : Plan) : (resetWrites plan).map Prod.fst = resetSites.map (cell plan .header) := by
  simp [resetWrites, resetSites]

theorem reset_site_bound (offset : Nat) (member : offset ∈ resetSites) : offset < 72 := by
  simp only [resetSites, List.mem_cons, List.not_mem_nil, or_false] at member
  omega

theorem reset_distinct (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) : ((resetWrites plan).map Prod.fst).Nodup := by
  rw [reset_cells]
  exact TableRuntime.header_sites_nodup kind plan valid resetSites reset_site_bound (by decide)

theorem clear_pool_away (memory : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (pool : Pool) (notUsed : pool ≠ .used) (offset : Nat) (inside : offset < size kind plan pool) :
    Zero.finalMemory memory (cell plan .used 0) plan.capacity (cell plan pool offset) = memory (cell plan pool offset) := by
  apply Zero.final_memory_away
  intro byte byteInside
  change cell plan pool offset ≠ cell plan .used 0 + BitVec.ofNat 64 byte
  rw [constant_cell]
  exact separate kind plan valid pool .used notUsed offset byte inside (used_offset_inside kind plan byte byteInside)

theorem reset_header_kept (memory : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (offset : Nat) (early : offset < 16) : resetMemory memory plan (cell plan .header offset) = memory (cell plan .header offset) := by
  rw [resetMemory, WordWrites.write_away]
  · exact clear_pool_away memory kind plan valid .header (by decide) offset (by change offset < 72; omega)
  · rw [reset_cells]
    intro member
    obtain ⟨other, belongs, same⟩ := List.mem_map.mp member
    have high := reset_site_bound other belongs
    have different : other ≠ offset := by
      simp only [resetSites, List.mem_cons, List.not_mem_nil, or_false] at belongs
      omega
    exact cell_injective kind plan valid .header other offset high (by change offset < 72; omega) different same

/-- All actual post-reset header words, retaining the unchanged key length
and stride cells instead of silently rewriting them. -/
theorem reset_header (memory : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (keyCell : memory (cell plan .header 0) = .word (BitVec.ofNat 64 (KeyHash.keySize kind)))
    (strideCell : memory (cell plan .header 8) = .word (BitVec.ofNat 64 (stride kind))) :
    MemoryModel.Header (resetMemory memory plan) kind plan 0#64 := by
  have stored (offset : Nat) (value : BitVec 64) (member : (cell plan .header offset, value) ∈ resetWrites plan) :
      resetMemory memory plan (cell plan .header offset) = .word value :=
    WordWrites.write_unique _ _ (cell plan .header offset, value) (reset_distinct kind plan valid) member
  intro offset value member
  simp only [MemoryModel.headerEntries, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (reset_header_kept memory kind plan valid 0 (by decide)).trans keyCell
  · exact (reset_header_kept memory kind plan valid 8 (by decide)).trans strideCell
  all_goals exact stored _ _ (by simp [resetWrites])

/-- The seven actual header stores preserve the zeroed used-byte array. -/
theorem reset_byte (memory : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (multiple : plan.capacity % 8 = 0) (offset : Nat) (inside : offset < plan.capacity) :
    ZeroBytes.read (resetMemory memory plan) (cell plan .used 0 + BitVec.ofNat 64 offset) = 0 := by
  have usedInside := used_offset_inside kind plan offset inside
  have queryCell : panByteAlignHOL (width := 64) (cell plan .used 0 + BitVec.ofNat 64 offset) = cell plan .used (8 * (offset / 8)) := by
    rw [constant_cell, byte_cell kind plan valid .used offset usedInside]
  have away : panByteAlignHOL (width := 64) (cell plan .used 0 + BitVec.ofNat 64 offset) ∉ (resetWrites plan).map Prod.fst := by
    rw [reset_cells, queryCell]
    intro member
    obtain ⟨other, belongs, same⟩ := List.mem_map.mp member
    exact separate kind plan valid .header .used (by decide) other _ (reset_site_bound other belongs) (by omega) same
  unfold ZeroBytes.read resetMemory
  rw [WordWrites.write_away _ _ _ away]
  have capHigh := valid.upper .used
  change plan.base .used + rounded plan.capacity ≤ 33806089496 at capHigh
  have roundHigh := (rounded_bounds plan.capacity).1
  exact ZeroBytes.final_byte memory _ plan.capacity offset multiple inside (by rw [base_number kind plan valid .used]; exact valid.aligned .used)
    (by rw [base_number kind plan valid .used]; omega)

theorem reset_model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (multiple : plan.capacity % 8 = 0) (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false) :
    MemoryModel.Occupied {source with memory := resetMemory source.memory plan} kind plan [] := by
  constructor
  · exact List.nodup_nil
  · intro slot impossible; cases impossible
  · intro slot inside
    classical
    have mapped : source.memaddrs (panByteAlignHOL (width := 64) (cell plan .used 0 + BitVec.ofNat 64 slot)) := by
      rw [domain, constant_cell]
      exact byte_mapped kind plan valid .used slot (used_offset_inside kind plan slot inside)
    have read := reset_byte source.memory kind plan valid multiple slot inside
    change @panMemLoadByteHOL 64 _ (resetMemory source.memory plan) source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be (cell plan .used 0 + BitVec.ofNat 64 slot) = some 0
    rw [little]
    cases stored : resetMemory source.memory plan (panByteAlignHOL (width := 64) (cell plan .used 0 + BitVec.ofNat 64 slot)) with
    | word value =>
      simp only [ZeroBytes.read, stored, MemoryBytes.wordBits] at read
      simp only [panMemLoadByteHOL, stored, if_pos mapped, read]
  · intro index; exact Fin.elim0 index
  · intro index; exact Fin.elim0 index

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.reset_distinct
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.clear_pool_away
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.reset_header_kept
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.reset_header
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.reset_byte
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.reset_model
