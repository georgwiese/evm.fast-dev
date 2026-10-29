import InitECandidate.Solver.PanFieldStores
import InitECandidate.Solver.MutableTable.MemoryRegionCore

namespace InitECandidate.Solver.FieldStores
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix MutableTable

theorem Value.ready_writes {F : Type} (source : PanSemStateFiniteExact 64 F) (base : BitVec 64) (fields : List Field)
    (messageName : String) (message : BitVec 64) (value : Value)
    (ready : value.Ready source messageName message)
    (separate : ∀ field ∈ fields, value.Avoid message (base + BitVec.ofNat 64 field.offset)) :
    value.Ready {source with memory := WordWrites.write source.memory (writes base fields)} messageName message := by
  cases value with
  | literal value => trivial
  | saved name value => exact ready
  | globalSaved name value => exact ready
  | copied offset value =>
    refine ⟨ready.1, ready.2.1, ?_⟩
    have away : message + BitVec.ofNat 64 offset ∉ (writes base fields).map Prod.fst := by
      intro member
      simp only [writes, List.map_map, Function.comp_def] at member
      obtain ⟨field, inside, same⟩ := List.mem_map.mp member
      exact separate field inside same.symm
    change WordWrites.write source.memory (writes base fields) (message + BitVec.ofNat 64 offset) = .word value
    rw [WordWrites.write_away source.memory _ _ away]
    exact ready.2.2

/-- Full scalar field-write lists retain all words outside the owning
message/record interval. This frame applies to actual copied-read stores. -/
theorem writes_outside (memory : WordWrites.Memory) (region : MemoryRegion.Region) (valid : MemoryRegion.Valid region) (fields : List Field)
    (inside : ∀ field ∈ fields, field.offset < region.length) (query : BitVec 64)
    (outside : query.toNat < region.start ∨ region.start + region.length ≤ query.toNat) :
    WordWrites.write memory (writes (MemoryRegion.pointer region) fields) query = memory query := by
  apply WordWrites.write_away
  intro member
  simp only [writes, List.map_map, Function.comp_def] at member
  obtain ⟨field, inFields, same⟩ := List.mem_map.mp member
  have number : (MemoryRegion.pointer region + BitVec.ofNat 64 field.offset).toNat = region.start + field.offset := by
    change (byteAddress (MemoryRegion.pointer region) field.offset).toNat = _
    rw [MemoryRegion.byte_address, MemoryRegion.address_number region valid field.offset (by have bound := inside field inFields; omega)]
  have numeric := congrArg BitVec.toNat same
  rw [number] at numeric
  have bound := inside field inFields
  omega

end InitECandidate.Solver.FieldStores

#print axioms InitECandidate.Solver.FieldStores.Value.ready_writes
#print axioms InitECandidate.Solver.FieldStores.writes_outside
