import InitECandidate.Solver.MutableTable.MemoryModelInsertFrame
import InitECandidate.Solver.MutableTable.MemoryModelValue
import InitECandidate.Solver.MutableTable.MemoryModelPoolFrame
import InitECandidate.Solver.MutableTable.SetEffect

namespace InitECandidate.Solver.MutableTable.TableFootprint
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

def Outside (kind : KeyHash.Kind) (plan : Plan) (address : BitVec 64) : Prop :=
  ∀ pool offset, offset < size kind plan pool → address ≠ cell plan pool offset
def Frame (input output : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) : Prop :=
  ∀ address, Outside kind plan address → output address = input address

theorem Outside.of_regions (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (address : BitVec 64)
    (outside : ∀ pool, address.toNat < plan.base pool ∨ plan.base pool + size kind plan pool ≤ address.toNat) :
    Outside kind plan address := by
  intro pool offset inside equal
  have numeric := congrArg BitVec.toNat equal
  rw [number kind plan valid pool offset inside] at numeric
  have apart := outside pool
  omega

theorem Frame.refl (memory : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) : Frame memory memory kind plan := by
  intro address outside; rfl

theorem Frame.trans (input middle output : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan)
    (first : Frame input middle kind plan) (second : Frame middle output kind plan) : Frame input output kind plan := by
  intro address outside
  exact (second address outside).trans (first address outside)

theorem inserted (input : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (query index count value : BitVec 64) (inside : index.toNat < plan.capacity) (countInside : count.toNat < plan.capacity) :
    Frame input (MemoryModel.insertedMemory input be kind plan query index count value) kind plan := by
  intro address outside
  apply MemoryModel.inserted_away input be kind plan valid query index count value address inside countInside
  · intro pool _ offset inPool
    exact outside pool offset inPool
  · exact outside .header 24 (by change 24 < 72; decide)

theorem updated (input : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan)
    (index value : BitVec 64) (inside : index.toNat < plan.capacity) :
    Frame input (MemoryModel.valueMemory input plan index value) kind plan := by
  intro address outside
  rw [MemoryModel.valueMemory, scaled_cell]
  exact if_neg (outside .values _ (word_offset_inside kind plan .values index.toNat (Or.inl rfl) inside))

/-- Every actual non-growing setter effect preserves all words outside
its six owned pools, so unrelated messages and frames can be carried. -/
theorem setter_effect (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (query count value : BitVec 64) (countInside : count.toNat < plan.capacity) (memory : WordWrites.Memory)
    (effect : Set.Effect source kind (parameters kind plan query) (cell plan .header 0)
      (cell plan .values 0) (cell plan .order 0) (cell plan .position 0) count value memory) : Frame source.memory memory kind plan := by
  have cap : (parameters kind plan query).capacity.toNat = plan.capacity := by
    change (BitVec.ofNat 64 plan.capacity).toNat = plan.capacity
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (capacity_small kind plan valid)]
  rcases effect with ⟨index, inside, _, rfl⟩ | ⟨index, inside, _, rfl⟩
  · exact updated source.memory kind plan index value (by rwa [cap] at inside)
  · exact inserted source.memory source.be kind plan valid query index count value (by rwa [cap] at inside) countInside

/-- Disjoint owners turn a writer's full footprint into the complete
pool frame required by the existing physical representation theorems. -/
theorem Frame.other_pools (input output : WordWrites.Memory) (writerKind readerKind : KeyHash.Kind) (writer reader : Plan)
    (writerValid : Valid writerKind writer) (readerValid : Valid readerKind reader)
    (apart : ∀ first second, writer.base first + size writerKind writer first ≤ reader.base second ∨ reader.base second + size readerKind reader second ≤ writer.base first)
    (frame : Frame input output writerKind writer) : MemoryModel.PoolFrame input output readerKind reader := by
  intro pool offset inside
  apply frame
  apply Outside.of_regions writerKind writer writerValid
  intro other
  rw [number readerKind reader readerValid pool offset inside]
  have ordered := apart other pool
  omega

end InitECandidate.Solver.MutableTable.TableFootprint

#print axioms InitECandidate.Solver.MutableTable.TableFootprint.Outside.of_regions
#print axioms InitECandidate.Solver.MutableTable.TableFootprint.Frame.refl
#print axioms InitECandidate.Solver.MutableTable.TableFootprint.Frame.trans
#print axioms InitECandidate.Solver.MutableTable.TableFootprint.inserted
#print axioms InitECandidate.Solver.MutableTable.TableFootprint.updated
#print axioms InitECandidate.Solver.MutableTable.TableFootprint.setter_effect
#print axioms InitECandidate.Solver.MutableTable.TableFootprint.Frame.other_pools
