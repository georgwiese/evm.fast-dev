import InitECandidate.Solver.WitnessRadix.ConstructorStep
import InitECandidate.Solver.WitnessRadix.AllocatedAway
import InitECandidate.Solver.WitnessRadix.MemoryAgreement

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack PanSemStateFiniteExact BackingLayout

structure PoolFrame {F : Type} (source target : PanSemStateFiniteExact 64 F) (layout : Layout) : Prop where
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  memory : ∀ pool offset,offset<size layout pool → target.memory (cell layout pool offset)=source.memory (cell layout pool offset)

theorem PoolFrame.prefix {F : Type} (source target : PanSemStateFiniteExact 64 F) (layout : Layout) (valid : Valid layout)
    (frame : PoolFrame source target layout) (keyFor : BitVec 64 → ByteKeys.Key) (done : Nat) (bound : done≤layout.count)
    (prefixData : Prefix source layout keyFor done) : Prefix target layout keyFor done := by
  have room := valid.room
  constructor
  · intro index inside
    exact (frame.memory .vals (8*index) (by change 8*index<8*layout.capacity; omega)).trans (prefixData.recordWords index inside)
  · intro index inside
    apply MemoryBytes.byteView_of_cells source target frame.domain.symm frame.endian.symm _ _ _ (prefixData.hashViews index inside)
    intro byte
    rw [MemoryBytes.aligned_offset _ byte.val byte.isLt (hash_aligned layout valid index (by omega)) (hash_fits layout valid index (by omega)),hash_limb_cell]
    exact (frame.memory .keys (32*index+8*(byte.val/8)) (by
      change 32*index+8*(byte.val/8)<32*layout.capacity
      have := byte.isLt
      omega)).symm
  · intro index inside
    exact (frame.memory .primary (8*index) (by change 8*index<8*layout.capacity; omega)).trans (prefixData.ordinalWords index inside)

theorem PoolFrame.fixed_data {F : Type} (source target : PanSemStateFiniteExact 64 F) (layout : Layout)
    (frame : PoolFrame source target layout) (sliceFor : BitVec 64 → Graph.Slice) (fixedData : FixedData source layout sliceFor) :
    FixedData target layout sliceFor := by
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
  · rw [frame.domain]; exact fixedData.header.keysMapped
  · exact (frame.memory .header 32 (by change 32<72; decide)).trans fixedData.header.keysWord
  · rw [frame.domain]; exact fixedData.header.valsMapped
  · exact (frame.memory .header 40 (by change 40<72; decide)).trans fixedData.header.valsWord
  · rw [frame.domain]; exact fixedData.header.srcMapped
  · exact (frame.memory .header 56 (by change 56<72; decide)).trans fixedData.header.srcWord
  · rw [frame.domain]; exact fixedData.header.dstMapped
  · exact (frame.memory .header 64 (by change 64<72; decide)).trans fixedData.header.dstWord
  · intro index inside
    exact (frame.memory .records (16*index) (by change 16*index<16*layout.count; omega)).trans (fixedData.pointers index inside)
  · intro index inside
    exact (frame.memory .records (16*index+8) (by change 16*index+8<16*layout.count; omega)).trans (fixedData.lengths index inside)

theorem PoolFrame.mapped {F : Type} (source target : PanSemStateFiniteExact 64 F) (layout : Layout)
    (frame : PoolFrame source target layout) (mapped : Mapped source layout) : Mapped target layout := by
  intro pool offset aligned inside
  rw [frame.domain]
  exact mapped pool offset aligned inside

theorem PoolFrame.of_hash (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (layout : Layout) (valid : Valid layout)
    (stp pointer scratch out : BitVec 64) (length : Nat) (buffers : Keccak256.Buffers stp pointer scratch out length)
    (control : KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl source)
    (memory : ∀ query,Keccak256.Protected stp scratch out query → target.memory query=source.memory query)
    (before : ∀ pool,stp.toNat+200≤(base layout pool).toNat ∧ scratch.toNat+136≤(base layout pool).toNat ∧ out.toNat+32≤(base layout pool).toNat) :
    PoolFrame source target layout := by
  constructor
  · have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memaddrs) control
    exact h
  · have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.be) control
    exact h
  · intro pool offset inside
    apply memory
    have bounds := before pool
    have number := byteAddress_toNat (base layout pool) offset (by have := valid.noWrap pool; omega)
    apply AllocatedBytes.protected_above stp pointer scratch out (cell layout pool offset) length buffers
    all_goals change _≤(byteAddress (base layout pool) offset).toNat; rw [number]; omega

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.PoolFrame.prefix
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.PoolFrame.fixed_data
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.PoolFrame.mapped
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.PoolFrame.of_hash
