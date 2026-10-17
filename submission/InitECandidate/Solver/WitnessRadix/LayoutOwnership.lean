import InitECandidate.Solver.WitnessRadix.ImmutableRecords
import InitECandidate.Solver.WitnessRadix.ScatterReady
import InitECandidate.Solver.WitnessRadix.LayoutSeparation

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact

def Mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) : Prop :=
  ∀ pool offset, offset % 8 = 0 → offset + 8 ≤ size layout pool → source.memaddrs (cell layout pool offset)

theorem row_cell (layout : Layout) (pool : Pool) (start index : Nat) :
    BuildCopy.row (base layout pool) (BitVec.ofNat 64 start) (BitVec.ofNat 64 index) =
      cell layout pool (8 * (start + index)) := by
  simp only [BuildCopy.row, cell, byteAddress, BitVec.ofNat_add, BitVec.ofNat_mul, Nat.mul_comm]

theorem buffer_cell (layout : Layout) (pool : Pool) (index : Nat) :
    ScatterProgram.wordAddress (base layout pool) index = cell layout pool (8 * index) := by
  simp only [ScatterProgram.wordAddress, cell, byteAddress, BitVec.ofNat_mul, Nat.mul_comm]

/-- Actual scatter ownership follows uniformly from the allocated pools,
immutable record views and a readable active interval of valid ordinals. -/
theorem ready {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (valid : Valid layout) (mapped : Mapped source layout)
    (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (immutable : Immutable source layout keyFor sliceFor) (input : List (BitVec 64)) (start : Nat)
    (fits : start + input.length ≤ layout.count)
    (ordinals : ∀ ordinal ∈ input, ordinal.toNat < layout.count)
    (rows : BuildCopy.Rows source.memory source.memaddrs layout.primary (BitVec.ofNat 64 start) 0 input) :
    ScatterProgram.Ready source layout.primary layout.backup (BitVec.ofNat 64 start) layout.keys keyFor input 0 layout.count := by
  have room := valid.room
  refine ⟨rows, ?_, ?_, ?_, ?_⟩
  · intro ordinal member
    simpa using immutable.views ordinal.toNat (ordinals ordinal member)
  · intro cursor bound
    change source.memaddrs (ScatterProgram.wordAddress (base layout .backup) cursor)
    rw [buffer_cell layout .backup cursor]
    exact mapped .backup (8 * cursor) (by omega) (by change 8 * cursor + 8 ≤ 8 * layout.capacity; omega)
  · intro cursor bound offset offsetBound
    change BuildCopy.row (base layout .primary) _ _ ≠ ScatterProgram.wordAddress (base layout .backup) cursor
    rw [row_cell, buffer_cell]
    exact valid.separate .primary .backup (by decide) _ (by change _ < 8 * layout.capacity; omega)
      _ (by change _ < 8 * layout.capacity; omega)
  · intro cursor bound ordinal member byte
    have ordinalBound := ordinals ordinal member
    have address := hash_byte_cell layout valid ordinal.toNat ordinalBound byte
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at address
    change panByteAlignHOL (width := 64) (layout.keys + ordinal * 32#64 + BitVec.ofNat 64 byte.val) ≠
      ScatterProgram.wordAddress (base layout .backup) cursor
    rw [address, buffer_cell layout .backup cursor]
    exact valid.separate .keys .backup (by decide) _
      (by change _ < 32 * layout.capacity; have := byte.isLt; omega)
      _ (by change _ < 8 * layout.capacity; omega)

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.ready
