import InitECandidate.Solver.WitnessRadix.MemoryRegionAgreement
import InitECandidate.Solver.WitnessRadix.ZeroMemory

namespace InitECandidate.Solver.WitnessRadix.Zero
open Flapjack MemoryRegion

theorem memory32_agrees (region : BitVec 64 → Prop) (left right : WordWrites.Memory)
    (same : Agree region left right) (dst : BitVec 64) (index blocks : Nat) :
    Agree region (memory32 left dst index blocks) (memory32 right dst index blocks) := by
  induction blocks generalizing left right index with
  | zero => exact same
  | succ blocks ih =>
    apply ih _ _ ?_ (index + 32)
    exact MemoryRegion.word_writes region left right same _

theorem memoryWord_agrees (region : BitVec 64 → Prop) (left right : WordWrites.Memory)
    (same : Agree region left right) (dst : BitVec 64) (index blocks : Nat) :
    Agree region (memoryWord left dst index blocks) (memoryWord right dst index blocks) := by
  induction blocks generalizing left right index with
  | zero => exact same
  | succ blocks ih =>
    exact ih _ _ (MemoryRegion.word_put region left right same (dst + BitVec.ofNat 64 index) 0#64) (index + 8)

theorem finalMemory_agrees (region : BitVec 64 → Prop) (left right : WordWrites.Memory)
    (same : Agree region left right) (dst : BitVec 64) (length : Nat) :
    Agree region (finalMemory left dst length) (finalMemory right dst length) :=
  memoryWord_agrees region _ _ (memory32_agrees region left right same dst 0 (length / 32))
    dst (32 * (length / 32)) ((length % 32) / 8)

end InitECandidate.Solver.WitnessRadix.Zero

#print axioms InitECandidate.Solver.WitnessRadix.Zero.memory32_agrees
#print axioms InitECandidate.Solver.WitnessRadix.Zero.memoryWord_agrees
#print axioms InitECandidate.Solver.WitnessRadix.Zero.finalMemory_agrees
