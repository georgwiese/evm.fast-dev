import InitECandidate.Solver.MutableTable.DeleteFinishMemory

namespace InitECandidate.Solver.MutableTable.Delete.Finish
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

theorem used_byte (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole) (query : Nat) (inside : query < plan.capacity) :
    Find.usedByte {source with memory := memory source.memory plan deleted entries hole} (parameters kind plan 0#64) (BitVec.ofNat 64 query) =
      if query = hole then some 0 else Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 query) := by
  let post := {source with memory := memory source.memory plan deleted entries hole}
  let cleared := {source with memory := clearedMemory source.memory plan hole}
  have queryExtent := used_offset_inside kind plan query inside
  have holeExtent := used_offset_inside kind plan hole pending.holeInside
  have queryCell : panByteAlignHOL (width := 64) ((parameters kind plan 0#64).used + BitVec.ofNat 64 query) = cell plan .used (8 * (query / 8)) := by
    change panByteAlignHOL (width := 64) (cell plan .used 0 + BitVec.ofNat 64 query) = _
    rw [constant_cell, byte_cell kind plan valid .used query queryExtent]
  have kept : Find.usedByte post (parameters kind plan 0#64) (BitVec.ofNat 64 query) = Find.usedByte cleared (parameters kind plan 0#64) (BitVec.ofNat 64 query) := by
    apply Find.usedByte_of_cell post cleared _ _ rfl rfl
    rw [queryCell]
    exact writes_pool_away _ kind plan valid count deleted entries pending.room pending.inside .used (by decide) (by decide) (by decide) _ (by omega)
  rw [kept]
  have sameAddress : (cell plan .used 0 + BitVec.ofNat 64 query = cell plan .used 0 + BitVec.ofNat 64 hole) ↔ query = hole := by
    rw [constant_cell, constant_cell]
    constructor
    · intro same
      have numeric := congrArg BitVec.toNat same
      rw [number kind plan valid .used query queryExtent, number kind plan valid .used hole holeExtent] at numeric
      omega
    · intro same; rw [same]
  have mappedHole : source.memaddrs (panByteAlignHOL (width := 64) (cell plan .used 0 + BitVec.ofNat 64 hole)) := by
    rw [domain, constant_cell]
    exact byte_mapped kind plan valid .used hole holeExtent
  have actual := ByteStore.read_write source (cell plan .used 0 + BitVec.ofNat 64 hole) (cell plan .used 0 + BitVec.ofNat 64 query) 0 little mappedHole
  simpa only [Find.usedByte, parameters, sameAddress, cleared, clearedMemory] using actual

theorem header_away (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole) (offset : Nat) (inside : offset < 72) (notCount : offset ≠ 24) :
    memory source.memory plan deleted entries hole (cell plan .header offset) = source.memory (cell plan .header offset) := by
  have ordinalInside : deleted.val < plan.capacity := Nat.lt_trans deleted.isLt pending.room
  have countAway := cell_injective kind plan valid .header offset 24 inside (by change 24 < 72; decide) notCount
  have away : cell plan .header offset ∉ (writes plan deleted entries).map Prod.fst := by
    by_cases last : deleted.val = count - 1
    · simpa only [writes, if_pos last, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] using countAway
    · have slotInside := pending.inside (lastOrdinal deleted) (last_active deleted last)
      have orderAway := separate kind plan valid .header .order (by decide) offset (8 * deleted.val) inside (by change 8 * deleted.val < 8 * plan.capacity; omega)
      have positionAway := separate kind plan valid .header .position (by decide) offset (8 * entries (lastOrdinal deleted)) inside (by change 8 * entries (lastOrdinal deleted) < 8 * plan.capacity; omega)
      simp only [writes, if_neg last, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨orderAway, positionAway, countAway⟩
  rw [memory, WordWrites.write_away _ _ _ away]
  exact cleared_pool_away _ kind plan valid hole pending.holeInside .header (by decide) offset inside

theorem count_cell (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole) :
    memory source.memory plan deleted entries hole (cell plan .header 24) = .word (BitVec.ofNat 64 (count - 1)) := by
  apply WordWrites.write_unique _ _ (cell plan .header 24, BitVec.ofNat 64 (count - 1)) (writes_distinct kind plan valid count deleted entries pending.room pending.inside)
  by_cases last : deleted.val = count - 1 <;> simp [writes, last]

theorem header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole)
    (old : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 count)) :
    MemoryModel.Header (memory source.memory plan deleted entries hole) kind plan (BitVec.ofNat 64 (count - 1)) := by
  have kept (offset : Nat) (inside : offset < 72) (notCount : offset ≠ 24) (value : BitVec 64)
      (member : (offset, value) ∈ MemoryModel.headerEntries kind plan (BitVec.ofNat 64 count)) :
      memory source.memory plan deleted entries hole (cell plan .header offset) = .word value :=
    (header_away source kind plan valid count deleted entries hole pending offset inside notCount).trans (old offset value member)
  intro offset value member
  simp only [MemoryModel.headerEntries, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact kept 0 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries])
  · exact kept 8 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries])
  · exact kept 16 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries])
  · exact count_cell source kind plan valid count deleted entries hole pending
  · exact kept 32 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries])
  · exact kept 40 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries])
  · exact kept 48 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries])
  · exact kept 56 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries])
  · exact kept 64 (by decide) (by decide) _ (by simp [MemoryModel.headerEntries])

end InitECandidate.Solver.MutableTable.Delete.Finish

#print axioms InitECandidate.Solver.MutableTable.Delete.Finish.used_byte
#print axioms InitECandidate.Solver.MutableTable.Delete.Finish.header_away
#print axioms InitECandidate.Solver.MutableTable.Delete.Finish.count_cell
#print axioms InitECandidate.Solver.MutableTable.Delete.Finish.header
