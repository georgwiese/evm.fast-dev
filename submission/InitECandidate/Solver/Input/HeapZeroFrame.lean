import InitECandidate.Solver.Input.HeapFrame
import InitECandidate.Solver.WitnessRadix.ZeroMemory

namespace InitECandidate.Solver.Input.Blob
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- A real zeroed allocation before/after the copied input preserves all
decoder bytes. Alignment is used for physical backing-word separation;
the mathematical input list remains unrestricted. -/
theorem HeapInput.zero_separate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer destination : BitVec 64) (length : Nat) (heap : HeapInput source input pointer)
    (aligned : pointer.toNat % 8 = 0) (fits : pointer.toNat + input.length % 2 ^ 64 < 2 ^ 64)
    (arena : AllocatedBytes.Arena destination length)
    (separate : destination.toNat + length ≤ pointer.toNat ∨ pointer.toNat + input.length % 2 ^ 64 ≤ destination.toNat) :
    HeapInput {source with memory := Zero.finalMemory source.memory destination length} input pointer := by
  intro offset inside
  have memory := Zero.final_memory_away source.memory destination (panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 offset)) length (by
    intro index member same
    have point := MemoryBytes.offset_toNat pointer offset (by omega)
    have current := byteAddress_toNat destination index (by have := arena.upper; omega)
    have equal := congrArg BitVec.toNat same
    rw [AllocatedBytes.aligned_number,point,current] at equal
    rcases separate with before | after <;> omega)
  have old := heap offset inside
  simpa only [panMemLoadByteHOL,memory] using old

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.HeapInput.zero_separate
