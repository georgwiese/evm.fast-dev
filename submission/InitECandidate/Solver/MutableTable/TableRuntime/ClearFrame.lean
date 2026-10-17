import InitECandidate.Solver.MutableTable.TableRuntime.Cells

namespace InitECandidate.Solver.MutableTable.TableRuntime
open Flapjack WitnessRadix NaturalLayout

/-- Both actual clear-memory branches preserve every other owned pool. -/
theorem clear_pool_away (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (start capacity : Nat)
    (valid : Valid kind (fresh kind start capacity)) (pool : Pool) (different : pool ≠ .used)
    (offset : Nat) (inside : offset < size kind (fresh kind start capacity) pool) :
    clearMemory memory be kind start capacity (cell (fresh kind start capacity) pool offset) = memory (cell (fresh kind start capacity) pool offset) := by
  have roundBound := (rounded_bounds capacity).1
  by_cases four : capacity = 4
  · simp only [clearMemory, if_pos four]
    apply Zero.memoryByte_away
    intro byte byteInside
    rw [Nat.zero_add]
    change cell (fresh kind start capacity) pool offset ≠ panByteAlignHOL (width := 64) (byteAddress (cell (fresh kind start capacity) .used 0) byte)
    rw [offset_cell, byte_cell kind _ valid .used byte (by change byte < rounded capacity; omega)]
    exact separate kind _ valid pool .used different offset _ inside (by change 8 * (byte / 8) < rounded capacity; omega)
  · simp only [clearMemory, if_neg four]
    apply Zero.final_memory_away
    intro byte byteInside
    change cell (fresh kind start capacity) pool offset ≠ byteAddress (cell (fresh kind start capacity) .used 0) byte
    rw [offset_cell]
    exact separate kind _ valid pool .used different offset byte inside (by change byte < rounded capacity; omega)

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.clear_pool_away
