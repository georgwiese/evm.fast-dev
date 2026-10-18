import InitECandidate.Solver.MutableTable.TruncateBudget
import InitECandidate.Solver.MutableTable.DeleteModelOwnership

namespace InitECandidate.Solver.MutableTable.Truncate
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

variable {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {kind : KeyHash.Kind} {plan : Plan}
  {count paid : Nat} {limit : BitVec 64} {memory : WordWrites.Memory} {slots : List Nat}

theorem ModelPost.protected_word (post : ModelPost source kind plan count limit paid memory target slots)
    (address : BitVec 64) (outside : TableFootprint.Outside kind plan address) : target.memory address = source.memory address := by
  have actual := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) post.frame
  change target.memory = memory at actual
  rw [actual]
  exact post.footprint address outside

/-- Covered original truncation, with any number of actual deletions,
preserves every unrelated owned table and protected frame/message word. -/
theorem ModelPost.other_model (post : ModelPost source kind plan count limit paid memory target slots)
    (valid : Valid kind plan) (readerKind : KeyHash.Kind) (reader : Plan) (readerValid : Valid readerKind reader)
    (apart : ∀ first second, plan.base first + size kind plan first ≤ reader.base second ∨ reader.base second + size readerKind reader second ≤ plan.base first)
    (readerSlots : List Nat) (header : MemoryModel.Header source.memory readerKind reader (BitVec.ofNat 64 readerSlots.length))
    (occupied : MemoryModel.Occupied source readerKind reader readerSlots) :
    MemoryModel.Header target.memory readerKind reader (BitVec.ofNat 64 readerSlots.length) ∧ MemoryModel.Occupied target readerKind reader readerSlots := by
  have actual := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) post.frame
  change target.memory = memory at actual
  have pools : MemoryModel.PoolFrame source.memory target.memory readerKind reader := by
    rw [actual]
    exact TableFootprint.Frame.other_pools source.memory memory kind readerKind plan reader valid readerValid apart post.footprint
  have domain := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) post.frame
  have endian := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) post.frame
  exact ⟨MemoryModel.Header.of_pool_frame source.memory target.memory readerKind reader _ header pools,
    MemoryModel.Occupied.of_pool_frame source target readerKind reader readerValid readerSlots occupied domain endian pools⟩

end InitECandidate.Solver.MutableTable.Truncate

#print axioms InitECandidate.Solver.MutableTable.Truncate.ModelPost.protected_word
#print axioms InitECandidate.Solver.MutableTable.Truncate.ModelPost.other_model
