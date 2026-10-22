import InitECandidate.Solver.Input.HeaderEncoding.Context

namespace InitECandidate.Solver.Input.HeaderEncoding
open Flapjack WitnessRadix

theorem FieldFacts.of_cells (original current : Memory) (header : BitVec 64) (field : Field)
    (same : ∀ offset≤240,current (address header offset)=original (address header offset))
    (facts : FieldFacts original header field) : FieldFacts current header field := by
  cases field with
  | bytes offset length=>
    change offset≤240 ∧ offset%8=0 ∧ length≤256 ∧
      AllocatedBytes.Arena (MemoryBytes.wordBits (current (address header offset))) length
    rw [same offset facts.1]
    exact facts
  | scalar offset=>exact facts
  | wide offset=>exact facts
  | extra=>
    simpa only [FieldFacts,wordAt,same 128 (by decide),same 136 (by decide)] using facts

end InitECandidate.Solver.Input.HeaderEncoding

#print axioms InitECandidate.Solver.Input.HeaderEncoding.FieldFacts.of_cells
