import InitECandidate.Solver.GasBudget.JournalRecordGeometry
import InitECandidate.Solver.MutableTable.FamilyMemoryFrame
import InitECandidate.Solver.WitnessRadix.WordWrites

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix WitnessRadix.QueryBranch MutableTable

def recordWrites {ι : Type} (objects : ι → TableFamily.Object) (base index : Nat) (entry : Entry ι) : List (BitVec 64 × BitVec 64) :=
  (List.finRange 4).map (fun field => (entryAddress base index field, entryWord objects entry field))

def recordState {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (objects : ι → TableFamily.Object)
    (base index : Nat) (entry : Entry ι) := {source with memory := WordWrites.write source.memory (recordWrites objects base index entry)}

theorem record_writes_distinct {ι : Type} (objects : ι → TableFamily.Object) (base cap index : Nat) (entry : Entry ι)
    (valid : MemoryRegion.Valid ⟨base, 32 * cap⟩) (inside : index < cap) :
    ((recordWrites objects base index entry).map Prod.fst).Nodup := by
  simp only [recordWrites, List.map_map, Function.comp_def]
  exact (List.nodup_finRange 4).map (fun left right same => (entry_injective base cap index index left right valid inside inside same).2)

theorem record_word {ι : Type} (memory : WordWrites.Memory) (objects : ι → TableFamily.Object) (base cap index : Nat) (entry : Entry ι)
    (valid : MemoryRegion.Valid ⟨base, 32 * cap⟩) (inside : index < cap) (field : Fin 4) :
    WordWrites.write memory (recordWrites objects base index entry) (entryAddress base index field) = .word (entryWord objects entry field) := by
  apply WordWrites.write_unique memory (recordWrites objects base index entry) (entryAddress base index field, entryWord objects entry field)
    (record_writes_distinct objects base cap index entry valid inside)
  exact List.mem_map.mpr ⟨field, by simp, rfl⟩

theorem record_earlier {ι : Type} (memory : WordWrites.Memory) (objects : ι → TableFamily.Object) (base cap count index : Nat) (entry : Entry ι)
    (valid : MemoryRegion.Valid ⟨base, 32 * cap⟩) (room : count < cap) (earlier : index < count) (field : Fin 4) :
    WordWrites.write memory (recordWrites objects base count entry) (entryAddress base index field) = memory (entryAddress base index field) := by
  apply WordWrites.write_away
  intro member
  simp only [recordWrites, List.map_map, Function.comp_def] at member
  obtain ⟨other, inRange, same⟩ := List.mem_map.mp member
  have indices := (entry_injective base cap count index other field valid room (by omega) same).1
  omega

/-- Appending all four real journal words preserves every table pool. -/
theorem record_models {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (objects : ι → TableFamily.Object)
    (base cap count cursor : Nat) (entry : Entry ι) (family : TableFamily.Model source cursor objects)
    (zone : Zone objects base cap cursor) (room : count < cap) :
    TableFamily.Model (recordState source objects base count entry) cursor objects := by
  apply family.of_pools (target := recordState source objects base count entry) rfl rfl rfl
  intro table pool offset inside
  apply WordWrites.write_away
  intro member
  simp only [recordWrites, List.map_map, Function.comp_def] at member
  obtain ⟨field, inRange, same⟩ := List.mem_map.mp member
  exact zone.separate count room field table pool offset inside same

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.record_writes_distinct
#print axioms InitECandidate.Solver.GasBudget.Journal.record_word
#print axioms InitECandidate.Solver.GasBudget.Journal.record_earlier
#print axioms InitECandidate.Solver.GasBudget.Journal.record_models
