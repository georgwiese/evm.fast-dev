import InitECandidate.Solver.WitnessRadix.CopyByteLoop

namespace InitECandidate.Solver.WitnessRadix.CopyBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def memoryWalk (memory : WordWrites.Memory) (be : Bool) (src dst : BitVec 64) (index step : Nat) (offsets : List Nat) : Nat → WordWrites.Memory
  | 0 => memory
  | rounds + 1 => memoryWalk (memoryMany memory be src dst (BitVec.ofNat 64 index) offsets) be src dst (index + step) step offsets rounds

theorem walk_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index step : Nat) (offsets : List Nat) (rounds : Nat) :
    emptyLocalsHOLFinite (walk source src dst index step offsets rounds) = emptyLocalsHOLFinite
      { source with memory := memoryWalk source.memory source.be src dst index step offsets rounds, clock := source.clock - rounds } := by
  induction rounds generalizing source index with
  | zero => rfl
  | succ rounds ih =>
    rw [walk, ih]
    have clock : source.clock - 1 - rounds = source.clock - (rounds + 1) := by omega
    simp only [advance, writeMany_frame, QueryBranch.bind, setVarHOLFinite, decClockHOLFinite, emptyLocalsHOLFinite, memoryWalk, clock]

theorem walk_other {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index step : Nat) (offsets : List Nat) (rounds : Nat)
    (name : MlS) (different : ofString "i" ≠ name) :
    (walk source src dst index step offsets rounds).locals.lookup name = source.locals.lookup name := by
  induction rounds generalizing source index with
  | zero => rfl
  | succ rounds ih =>
    rw [walk, ih, advance_other _ _ _ _ _ _ _ different]
    rfl

theorem walk_index {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index step : Nat) (offsets : List Nat) (rounds : Nat)
    (initial : source.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 index)))) :
    (walk source src dst index step offsets rounds).locals.lookup (ofString "i") =
      some (.val (.word (BitVec.ofNat 64 (index + step * rounds)))) := by
  induction rounds generalizing source index with
  | zero => simpa only [walk, Nat.mul_zero, Nat.add_zero] using initial
  | succ rounds ih =>
    rw [walk]
    have next := ih _ (index + step) (by
      simpa only [BitVec.ofNat_add] using advance_index (decClockHOLFinite source) src dst
        (BitVec.ofNat 64 index) offsets (BitVec.ofNat 64 step))
    have total : index + step + step * rounds = index + step * (rounds + 1) := by rw [Nat.mul_succ]; omega
    simpa only [total] using next

theorem memoryWalk_away (memory : WordWrites.Memory) (be : Bool) (src dst query : BitVec 64) (index step : Nat) (offsets : List Nat) (rounds : Nat)
    (offsetBound : ∀ offset ∈ offsets, offset < step)
    (away : ∀ offset, index ≤ offset → offset < index + step * rounds →
      query ≠ panByteAlignHOL (width := 64) (byteAddress dst offset)) :
    memoryWalk memory be src dst index step offsets rounds query = memory query := by
  induction rounds generalizing memory index with
  | zero => rfl
  | succ rounds ih =>
    rw [memoryWalk, ih _ (index + step) (by
      intro offset low high
      apply away offset (by omega)
      simp only [Nat.mul_succ] at high ⊢
      omega)]
    apply memoryMany_away
    intro offset member
    have bound := offsetBound offset member
    have h := away (index + offset) (by omega) (by simp only [Nat.mul_succ]; omega)
    simpa only [byteAddress, BitVec.ofNat_add, BitVec.add_assoc] using h

end InitECandidate.Solver.WitnessRadix.CopyBytes

#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.walk_frame
#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.walk_other
#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.walk_index
#print axioms InitECandidate.Solver.WitnessRadix.CopyBytes.memoryWalk_away
