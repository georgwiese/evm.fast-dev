import InitECandidate.Solver.MutableTable.SetModelHeap

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString Flapjack.Pancake.PanLang

variable {source : PanSemStateFiniteExact 64 Guest.HostMemory} {kind : KeyHash.Kind} {old : Plan} {start count paid : Nat}
  {globals : HolFiniteMapExact MlS (ValueHOL 64)} {memory : WordWrites.Memory} {target : PanSemStateFiniteExact 64 Guest.HostMemory}
  {plan : Plan} {slots : List Nat}

/-- The complete original setter preserves each protected physical word,
including message gas and parent frame cells outside the written pools. -/
theorem ModelPost.protected_word (post : ModelPost source kind old start count paid globals memory target plan slots)
    (address : BitVec 64) (outside : TableFootprint.Outside kind plan address) : target.memory address = source.memory address := by
  have actual := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) post.frame
  change target.memory = memory at actual
  rw [actual]
  exact post.footprint address outside

theorem ModelPost.pool_floor (post : ModelPost source kind old start count paid globals memory target plan slots)
    (floor : Nat) (lower : ∀ pool, floor ≤ old.base pool)
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start) : ∀ pool, floor ≤ plan.base pool := by
  rcases post.shape with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact lower
  · intro pool
    have before := earlier .header
    have low := lower .header
    change old.base .header + 72 ≤ start at before
    cases pool <;> simp only [relocated] <;> omega

/-- Objects allocated before this table's lifetime retain their words
through every subsequent original setter growth. -/
theorem ModelPost.protected_before (post : ModelPost source kind old start count paid globals memory target plan slots)
    (valid : Valid kind plan) (floor : Nat) (lower : ∀ pool, floor ≤ old.base pool)
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (address : BitVec 64) (before : address.toNat < floor) : target.memory address = source.memory address := by
  apply post.protected_word address
  apply TableFootprint.Outside.of_regions kind plan valid address
  intro pool
  left
  have bounded := post.pool_floor floor lower earlier pool
  omega

theorem ModelPost.other_pools (post : ModelPost source kind old start count paid globals memory target plan slots)
    (valid : Valid kind plan) (readerKind : KeyHash.Kind) (reader : Plan) (readerValid : Valid readerKind reader)
    (apart : ∀ first second, plan.base first + size kind plan first ≤ reader.base second ∨ reader.base second + size readerKind reader second ≤ plan.base first) :
    MemoryModel.PoolFrame source.memory target.memory readerKind reader := by
  have actual := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) post.frame
  change target.memory = memory at actual
  rw [actual]
  exact TableFootprint.Frame.other_pools source.memory memory kind readerKind plan reader valid readerValid apart post.footprint

/-- Carry another live table's complete physical representation across an
actual setter return, including growth and caller restoration. -/
theorem ModelPost.other_model (post : ModelPost source kind old start count paid globals memory target plan slots)
    (valid : Valid kind plan) (readerKind : KeyHash.Kind) (reader : Plan) (readerValid : Valid readerKind reader)
    (apart : ∀ first second, plan.base first + size kind plan first ≤ reader.base second ∨ reader.base second + size readerKind reader second ≤ plan.base first)
    (readerSlots : List Nat) (header : MemoryModel.Header source.memory readerKind reader (BitVec.ofNat 64 readerSlots.length))
    (occupied : MemoryModel.Occupied source readerKind reader readerSlots) :
    MemoryModel.Header target.memory readerKind reader (BitVec.ofNat 64 readerSlots.length) ∧ MemoryModel.Occupied target readerKind reader readerSlots := by
  have pools := post.other_pools valid readerKind reader readerValid apart
  have domain := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) post.frame
  have endian := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) post.frame
  exact ⟨MemoryModel.Header.of_pool_frame source.memory target.memory readerKind reader _ header pools,
    MemoryModel.Occupied.of_pool_frame source target readerKind reader readerValid readerSlots occupied domain endian pools⟩

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.protected_word
#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.pool_floor
#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.protected_before
#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.other_pools
#print axioms InitECandidate.Solver.MutableTable.Set.ModelPost.other_model
