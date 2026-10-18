import InitECandidate.Solver.MutableTable.DeleteModelBudget

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

variable {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {kind : KeyHash.Kind} {plan : Plan}
  {slots next : List Nat} {paid : Nat} {memory : WordWrites.Memory} {flag : BitVec 64}

theorem ModelPost.protected_word (post : ModelPost source kind plan slots paid memory target next flag)
    (address : BitVec 64) (outside : TableFootprint.Outside kind plan address) : target.memory address = source.memory address := by
  have actual := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) post.frame
  change target.memory = memory at actual
  rw [actual]
  exact post.footprint address outside

/-- Every unrelated owned table retains its header and complete physical
occupied representation across actual original deletion. -/
theorem ModelPost.other_model (post : ModelPost source kind plan slots paid memory target next flag)
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

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.ModelPost.protected_word
#print axioms InitECandidate.Solver.MutableTable.Delete.ModelPost.other_model
