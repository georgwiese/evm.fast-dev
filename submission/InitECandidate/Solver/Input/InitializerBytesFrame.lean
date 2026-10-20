import InitECandidate.Solver.Input.InitializerBytes
import InitECandidate.Solver.WitnessRadix.ByteArrayReads
import InitECandidate.Solver.Rlp.SliceArrayModel

namespace InitECandidate.Solver.Input.InitializerBytes
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Untouched backing words survive the actual ordered partial-word updates. -/
theorem write_away (memory : WordWrites.Memory) (endian : Bool) (pointer query : BitVec 64) (offset : Nat) (bytes : List (BitVec 8))
    (away : ∀ position < bytes.length,query ≠ panByteAlignHOL (width := 64) (byteAddress pointer (offset + position))) :
    write memory endian pointer offset bytes query = memory query := by
  induction bytes generalizing memory offset with
  | nil => rfl
  | cons byte rest ih =>
    have tail := ih (ByteStore.put memory endian (byteAddress pointer offset) byte) (offset + 1) (by
      intro position inside
      have current := away (position + 1) (by simp only [List.length_cons]; omega)
      simpa only [Nat.add_assoc,Nat.add_comm 1 position] using current)
    have head : query ≠ panByteAlignHOL (width := 64) (byteAddress pointer offset) := by
      simpa only [Nat.add_zero] using away 0 (by simp)
    exact tail.trans (ByteStore.away memory endian (byteAddress pointer offset) query byte head)

/-- Earlier and later physical words survive an aligned bounded literal
byte-store prefix, including arbitrary initial contents of its boundary words. -/
theorem written_window (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (offset extent : Nat) (bytes : List (BitVec 8))
    (arena : AllocatedBytes.Arena pointer extent) (aligned : pointer.toNat % 8 = 0) (inside : offset + bytes.length ≤ extent) :
    Rlp.Slices.Window source (written source pointer offset bytes) pointer.toNat (pointer.toNat + extent) := by
  intro query outside
  apply write_away
  intro position member same
  have bounded : offset + position < extent := by omega
  have fits : pointer.toNat + extent < 2 ^ 64 := by have := arena.upper; omega
  have cell := ByteArray.aligned_cell pointer (offset + position) extent bounded aligned fits
  have equal := congrArg BitVec.toNat (same.trans cell)
  rw [byteAddress_toNat pointer (8 * ((offset + position) / 8)) (by omega)] at equal
  rcases outside with before | after <;> omega

end InitECandidate.Solver.Input.InitializerBytes

#print axioms InitECandidate.Solver.Input.InitializerBytes.write_away
#print axioms InitECandidate.Solver.Input.InitializerBytes.written_window
