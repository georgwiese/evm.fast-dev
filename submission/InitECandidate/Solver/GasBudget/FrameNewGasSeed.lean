import InitECandidate.Solver.GasBudget.FrameNewFreshCanonical
import InitECandidate.Solver.GasBudget.GasSeed

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack PanSemStateFiniteExact
open WitnessRadix

theorem fields_seed (memory : Memory) (frame mark pointer : BitVec 64) (words : MessageWords)
    (used : memory (frame + 184#64) = .word 0#64) (spill : memory (frame + 192#64) = .word 0#64) :
    GasSeed (WordWrites.write memory (FieldStores.writes frame (fields mark pointer words))) frame words.gas := by
  have distinct : ((FieldStores.writes frame (fields mark pointer words)).map Prod.fst).Nodup := by
    simp [FieldStores.writes, fields, BitVec.add_right_inj]
  refine ⟨WordWrites.write_unique memory _ (frame + 64#64, words.gas) distinct (by simp [FieldStores.writes, fields, FieldStores.Value.word]), ?_, ?_⟩
  · rw [WordWrites.write_away]
    · exact used
    · simp [FieldStores.writes, fields, BitVec.add_right_inj]
  · rw [WordWrites.write_away]
    · exact spill
    · simp [FieldStores.writes, fields, BitVec.add_right_inj]

theorem initialized_seed (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame memory mark : BitVec 64) (words : MessageWords)
    (used : source.memory (frame + 184#64) = .word 0#64) (spill : source.memory (frame + 192#64) = .word 0#64) :
    GasSeed (initialized source frame memory mark words).memory frame words.gas := by
  have keptUsed : (memoryAllocated source frame memory mark).memory (frame + 184#64) = .word 0#64 := by
    rw [allocation_memory_away]
    · exact used
    · simp [FieldStores.writes, stackFields, BitVec.add_right_inj]
  have keptSpill : (memoryAllocated source frame memory mark).memory (frame + 192#64) = .word 0#64 := by
    rw [allocation_memory_away]
    · exact spill
    · simp [FieldStores.writes, stackFields, BitVec.add_right_inj]
  exact fields_seed _ frame memory memory words keptUsed keptSpill

/-- Actual original clear/allocation/field initialization supplies zero used
and spill plus the incoming message gas, without a zero-counter premise. -/
theorem fresh_seed (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch memory : BitVec 64) (words : MessageWords) :
    GasSeed (fresh source scratch memory words).memory (Arenas.rounded .down scratch 280#64) words.gas :=
  initialized_seed (zeroed source scratch memory) _ memory scratch words
    (zeroed_cell source scratch memory 23 (by decide)) (zeroed_cell source scratch memory 24 (by decide))

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.fields_seed
#print axioms InitECandidate.Solver.GasBudget.FrameNew.initialized_seed
#print axioms InitECandidate.Solver.GasBudget.FrameNew.fresh_seed
