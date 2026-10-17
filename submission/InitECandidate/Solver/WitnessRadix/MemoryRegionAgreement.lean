import InitECandidate.Solver.WitnessRadix.ByteStore
import InitECandidate.Solver.WitnessRadix.WordWrites

namespace InitECandidate.Solver.WitnessRadix.MemoryRegion
open Flapjack

def Agree (region : BitVec 64 → Prop) (left right : WordWrites.Memory) : Prop :=
  ∀ query, region query → left query = right query

theorem word_put (region : BitVec 64 → Prop) (left right : WordWrites.Memory)
    (same : Agree region left right) (address value : BitVec 64) :
    Agree region (StoreWord.put left address value) (StoreWord.put right address value) := by
  intro query inside
  unfold StoreWord.put
  split
  · rfl
  · exact same query inside

theorem byte_put (region : BitVec 64 → Prop) (left right : WordWrites.Memory)
    (same : Agree region left right) (endian : Bool) (address : BitVec 64) (value : BitVec 8) :
    Agree region (ByteStore.put left endian address value) (ByteStore.put right endian address value) := by
  intro query inside
  unfold ByteStore.put StoreWord.put
  split
  · rename_i hit
    rw [same _ (hit ▸ inside)]
  · exact same query inside

theorem word_writes (region : BitVec 64 → Prop) (left right : WordWrites.Memory)
    (same : Agree region left right) (writes : List (BitVec 64 × BitVec 64)) :
    Agree region (WordWrites.write left writes) (WordWrites.write right writes) := by
  intro query inside
  rw [WordWrites.write_at, WordWrites.write_at]
  cases lastValue query writes with
  | none => exact same query inside
  | some value => rfl

end InitECandidate.Solver.WitnessRadix.MemoryRegion

#print axioms InitECandidate.Solver.WitnessRadix.MemoryRegion.word_put
#print axioms InitECandidate.Solver.WitnessRadix.MemoryRegion.byte_put
#print axioms InitECandidate.Solver.WitnessRadix.MemoryRegion.word_writes
