import InitECandidate.Solver.GasBudget.FrameNewSuffixLayout
import InitECandidate.Solver.GasBudget.FrameNewFreshFields

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack

def framePointer (scratch : BitVec 64) : BitVec 64 := Arenas.rounded .down scratch 280#64
def stackPointer (scratch : BitVec 64) : BitVec 64 := Arenas.rounded .down (framePointer scratch) 1024#64
def memoryPointer (lower : BitVec 64) : BitVec 64 := Arenas.rounded .up lower 1024#64

/-- Exact original frame/stack/memory geometry. The280-byte frame,1024-byte
stack,1024-byte frame-memory region,56-byte log list and272-byte delete table
reserve2656bytes in addition to the actual jump bitmap. -/
theorem construction_geometry (scratch lower : BitVec 64) (bitmapSize : Nat)
    (scratchAligned : scratch.toNat % 8 = 0) (lowerAligned : lower.toNat % 8 = 0)
    (bitmapPositive : 8 ≤ bitmapSize) (room : lower.toNat + bitmapSize + 2656 ≤ scratch.toNat) :
    (framePointer scratch).toNat = scratch.toNat - 280 ∧
    (framePointer scratch).toNat % 8 = 0 ∧
    (stackPointer scratch).toNat = scratch.toNat - 1304 ∧
    (stackPointer scratch).toNat % 8 = 0 ∧
    (memoryPointer lower).toNat = lower.toNat + 1024 ∧
    (memoryPointer lower).toNat % 8 = 0 ∧
    (framePointer scratch).toNat + 280 < 2 ^ 64 ∧
    lower.toNat + 280 ≤ scratch.toNat ∧
    lower.toNat + 2055 ≤ (framePointer scratch).toNat ∧
    (memoryPointer lower).toNat + bitmapSize + 328 ≤ (stackPointer scratch).toNat ∧
    (stackPointer scratch).toNat ≤ (framePointer scratch).toNat ∧
    (memoryPointer lower).toNat ≤ (framePointer scratch).toNat := by
  have bound := scratch.isLt
  have frameRounded := Arenas.rounded_down_nat scratch 280#64
    (by change 280 ≤ scratch.toNat; omega)
  have frameNumber : (framePointer scratch).toNat = scratch.toNat - 280 := by
    change (framePointer scratch).toNat = (scratch.toNat - 280) / 8 * 8 at frameRounded
    omega
  have frameAligned : (framePointer scratch).toNat % 8 = 0 := by rw [frameNumber]; omega
  have stackRounded := Arenas.rounded_down_nat (framePointer scratch) 1024#64
    (by change 1024 ≤ (framePointer scratch).toNat; omega)
  have stackNumber : (stackPointer scratch).toNat = scratch.toNat - 1304 := by
    change (stackPointer scratch).toNat = ((framePointer scratch).toNat - 1024) / 8 * 8 at stackRounded
    omega
  have memRounded := WitnessRadix.PersistentAlloc.rounded_nat lower 1024#64
    (by change lower.toNat + 1024 + 7 < 2 ^ 64; omega)
  have memoryNumber : (memoryPointer lower).toNat = lower.toNat + 1024 := by
    change (memoryPointer lower).toNat = (lower.toNat + 1024 + 7) / 8 * 8 at memRounded
    omega
  refine ⟨frameNumber, frameAligned, stackNumber, ?_, memoryNumber, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.construction_geometry
