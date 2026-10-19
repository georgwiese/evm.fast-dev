import InitECandidate.Solver.GasBudget.MemoryBufferOwnership
import InitECandidate.Solver.WitnessRadix.CopyNormalCall

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem View.span_arena {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame base length capacity pointer scratch : BitVec 64}
    (view : View source frame base length capacity pointer scratch) (start : BitVec 64) (count : Nat)
    (range : start.toNat + count ≤ length.toNat)
    (lower : 2701131776 ≤ base.toNat) (upper : scratch.toNat ≤ 33806089496) :
    AllocatedBytes.Arena (base + start) count := by
  have depth := view.depth
  have cursor := view.cursor
  have ordered := BitVec.le_def.mp view.ordered
  have scratchBound := scratch.isLt
  have number := BitVec.toNat_add_of_lt (show base.toNat + start.toNat < 2 ^ 64 by omega)
  exact ⟨by rw [number]; omega, by rw [number]; omega⟩

theorem View.copy_away {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame base length capacity pointer scratch : BitVec 64}
    (view : View source frame base length capacity pointer scratch) (start : BitVec 64) (count : Nat)
    (range : start.toNat + count ≤ length.toNat) (query : BitVec 64) (outside : Arenas.Outside base scratch query) :
    CopyGeneral.Away (base + start) query count := by
  intro offset inside
  obtain ⟨mapped, low, high⟩ := view.byte_owned start count offset range inside
  have aligned := AllocatedBytes.aligned_number (byteAddress (base + start) offset)
  have division := Nat.mod_add_div (byteAddress (base + start) offset).toNat 8
  constructor
  · intro equal
    have number := congrArg BitVec.toNat equal
    rcases outside with before | after <;> omega
  · exact view.byte_away start count offset range inside query outside

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.View.span_arena
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.View.copy_away
