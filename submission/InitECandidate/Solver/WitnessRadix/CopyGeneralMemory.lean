import InitECandidate.Solver.WitnessRadix.CopyGeneral

namespace InitECandidate.Solver.WitnessRadix.CopyContext
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem byte_walk_memory {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index step rounds : Nat) (offsets : List Nat) :
    (CopyBytes.walk source src dst index step offsets rounds).memory = CopyBytes.memoryWalk source.memory source.be src dst index step offsets rounds := by
  have h := congrArg (fun state : PanSemStateFiniteExact 64 F => state.memory) (CopyBytes.walk_frame source src dst index step offsets rounds)
  exact h

theorem word_walk_memory {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (index step rounds : Nat) (offsets : List Nat) :
    (CopyWords.walk source src dst index step offsets rounds).memory = CopyWords.memoryWalk source.memory src dst index step offsets rounds := by
  have h := congrArg (fun state : PanSemStateFiniteExact 64 F => state.memory) (CopyWords.walk_frame source src dst index step offsets rounds)
  exact h

theorem prefix_memory_away {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst query : BitVec 64) (length : Nat)
    (away : ∀ offset < length, query ≠ byteAddress dst offset) :
    (CopyWords.prefixState source src dst length).memory query = source.memory query := by
  have bounds := (CopyWords.prefix_bounds length).1
  unfold CopyWords.prefixIndex at bounds
  rw [CopyWords.prefixState, word_walk_memory, CopyWords.memoryWalk_away _ _ _ _ _ _ _ _
    (by intro offset member; simp at member; subst offset; decide)
    (by intro offset low high; exact away offset (by omega))]
  rw [word_walk_memory]
  apply CopyWords.memoryWalk_away
  · intro offset member
    simp [CopyWords.wordOffsets] at member
    omega
  · intro offset low high
    apply away offset
    omega

theorem suffix_memory_away {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst query : BitVec 64) (index length : Nat)
    (ordered : index ≤ length)
    (away : ∀ offset < length, query ≠ panByteAlignHOL (width := 64) (byteAddress dst offset)) :
    (CopyBytes.suffixState source src dst index length).memory query = source.memory query := by
  have div := Nat.mod_add_div (length-index) 8
  have total : index + 8*((length-index)/8) + (length-index)%8 = length := by omega
  rw [CopyBytes.suffixState, byte_walk_memory, CopyBytes.memoryWalk_away _ _ _ _ _ _ _ _ _
    (by intro offset member; simp at member; subst offset; decide)
    (by intro offset low high; exact away offset (by omega))]
  rw [byte_walk_memory]
  apply CopyBytes.memoryWalk_away
  · intro offset member
    simp [CopyBytes.byteOffsets] at member
    omega
  · intro offset low high
    apply away offset
    omega

end InitECandidate.Solver.WitnessRadix.CopyContext

namespace InitECandidate.Solver.WitnessRadix.CopyGeneral
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open CopyContext

def Away (dst query : BitVec 64) (length : Nat) : Prop :=
  ∀ offset < length, query ≠ byteAddress dst offset ∧ query ≠ panByteAlignHOL (width := 64) (byteAddress dst offset)

theorem core_memory_away {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst query : BitVec 64) (length : Nat)
    (away : Away dst query length) : (coreState source src dst length).memory query = source.memory query := by
  unfold coreState
  split
  · rw [suffix_memory_away _ _ _ _ _ _ (CopyWords.prefix_bounds length).1 (by intro offset high; exact (away offset high).2)]
    exact prefix_memory_away _ _ _ _ _ (by intro offset high; exact (away offset high).1)
  · exact suffix_memory_away _ _ _ _ _ _ (Nat.zero_le _) (by intro offset high; exact (away offset high).2)

end InitECandidate.Solver.WitnessRadix.CopyGeneral

#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.byte_walk_memory
#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.word_walk_memory
#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.prefix_memory_away
#print axioms InitECandidate.Solver.WitnessRadix.CopyContext.suffix_memory_away
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.core_memory_away
