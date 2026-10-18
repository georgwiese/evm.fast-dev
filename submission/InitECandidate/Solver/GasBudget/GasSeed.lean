import InitECandidate.Solver.GasBudget.FrameSums

namespace InitECandidate.Solver.GasBudget
open Flapjack

/-- Exact initial physical regular-gas cells of a fresh frame. -/
structure GasSeed (memory : Memory) (frame gas : BitVec 64) : Prop where
  liquid : memory (frame + 64#64) = .word gas
  used : memory (frame + 184#64) = .word 0#64
  spill : memory (frame + 192#64) = .word 0#64

theorem GasSeed.budget {memory : Memory} {frame gas : BitVec 64} (seed : GasSeed memory frame gas) :
    regularBudget memory frame = gas.toNat := by
  simp only [regularBudget, wordAt, seed.liquid, seed.used, seed.spill, WitnessRadix.MemoryBytes.wordBits, BitVec.toNat_zero, Nat.add_zero]

theorem GasSeed.transfer {before after : Memory} {frame gas : BitVec 64} (seed : GasSeed before frame gas)
    (same : ∀ offset ∈ ([64, 184, 192] : List Nat), after (frame + BitVec.ofNat 64 offset) = before (frame + BitVec.ofNat 64 offset)) : GasSeed after frame gas :=
  ⟨(same 64 (by simp)).trans seed.liquid, (same 184 (by simp)).trans seed.used, (same 192 (by simp)).trans seed.spill⟩

theorem GasSeed.insert {memory : Memory} {frame gas : BitVec 64} (seed : GasSeed memory frame gas) (frames : List (BitVec 64)) :
    FrameSums.budget memory (frame :: frames) = gas.toNat + FrameSums.budget memory frames ∧
      FrameSums.used memory (frame :: frames) = FrameSums.used memory frames :=
  FrameSums.add_child memory frames frame gas.toNat seed.budget seed.used

end InitECandidate.Solver.GasBudget

#print axioms InitECandidate.Solver.GasBudget.GasSeed.budget
#print axioms InitECandidate.Solver.GasBudget.GasSeed.transfer
#print axioms InitECandidate.Solver.GasBudget.GasSeed.insert
