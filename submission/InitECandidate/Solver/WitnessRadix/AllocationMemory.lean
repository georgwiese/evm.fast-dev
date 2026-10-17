import InitECandidate.Solver.WitnessRadix.AllocationCode
import InitECandidate.Solver.WitnessRadix.WordWrites

namespace InitECandidate.Solver.WitnessRadix.SplitProgram
open Flapjack

def allocationWrites (node depth start count zeros bit dest pendingStart pendingCount pendingNode : BitVec 64) :
    List (BitVec 64 × BitVec 64) :=
  [(node, bit), (node + 8#64, 0#64), (node + 16#64, 0#64), (dest, node),
   (pendingStart + depth * 8#64, start + zeros), (pendingCount + depth * 8#64, count - zeros),
   (pendingNode + depth * 8#64, node)]

theorem branchMemory_write (memory : WordWrites.Memory)
    (node depth start count zeros bit dest pendingStart pendingCount pendingNode : BitVec 64) :
    branchMemory memory node depth start count zeros bit dest pendingStart pendingCount pendingNode =
      WordWrites.write memory (allocationWrites node depth start count zeros bit dest pendingStart pendingCount pendingNode) := rfl

/-- All seven actual post-store words, under explicit nonaliasing. -/
theorem branchMemory_words (memory : WordWrites.Memory)
    (node depth start count zeros bit dest pendingStart pendingCount pendingNode : BitVec 64)
    (distinct : ((allocationWrites node depth start count zeros bit dest pendingStart pendingCount pendingNode).map Prod.fst).Nodup)
    (entry : BitVec 64 × BitVec 64)
    (member : entry ∈ allocationWrites node depth start count zeros bit dest pendingStart pendingCount pendingNode) :
    branchMemory memory node depth start count zeros bit dest pendingStart pendingCount pendingNode entry.1 = .word entry.2 := by
  rw [branchMemory_write]
  exact WordWrites.write_unique memory _ entry distinct member

theorem branchMemory_frame (memory : WordWrites.Memory)
    (node depth start count zeros bit dest pendingStart pendingCount pendingNode query : BitVec 64)
    (away : query ∉ (allocationWrites node depth start count zeros bit dest pendingStart pendingCount pendingNode).map Prod.fst) :
    branchMemory memory node depth start count zeros bit dest pendingStart pendingCount pendingNode query = memory query := by
  rw [branchMemory_write]
  exact WordWrites.write_away memory _ query away

end InitECandidate.Solver.WitnessRadix.SplitProgram

#print axioms InitECandidate.Solver.WitnessRadix.SplitProgram.branchMemory_words
#print axioms InitECandidate.Solver.WitnessRadix.SplitProgram.branchMemory_frame
