import InitECandidate.Solver.Mpt.WsAccountOptionalCallImage
import InitECandidate.Solver.MutableTable.FamilyAdvancePools
import InitECandidate.Solver.WitnessRadix.CopyAwayIntervals

namespace InitECandidate.Solver.Mpt.WsAccountOptional
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix MutableTable NaturalLayout

/-- All current live table pools lie beyond scratch/input cutoff and the
three fixed hash/nibble buffers. These are current lifetime-floor facts. -/
def FamilySeparated {ι : Type} (objects : ι → TableFamily.Object) (cutoff : Nat) (stp pad nibs : BitVec 64) : Prop :=
  ∀ index,cutoff≤(objects index).floor ∧ stp.toNat+200≤(objects index).floor ∧
    pad.toNat+136≤(objects index).floor ∧ nibs.toNat+64≤(objects index).floor

/-- The provider's derived ordinary-word frame retains every real table
pool. Allocation changes only the common cursor, by exactly0 or120 bytes. -/
theorem Result.family {ι : Type} (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor limit stp pad nibs : BitVec 64) (cutoff : Nat) (objects : ι → TableFamily.Object)
    (family : TableFamily.Model source heap.toNat objects) (separate : FamilySeparated objects cutoff stp pad nibs)
    (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0) (scratchBelow : cursor.toNat≤cutoff)
    (domain : post.memaddrs=source.memaddrs) (endian : post.be=source.be)
    (returned : ValueHOL 64) (result : Result post heap cursor limit returned)
    (memory : ∀ query : BitVec 64,cursor.toNat≤query.toNat → query.toNat<heap.toNat → Keccak256.Protected stp pad heap query →
      (∀ offset<64,query≠panByteAlignHOL (width:=64) (byteAddress nibs offset)) → post.memory query=source.memory query) :
    ∃ nextCursor,(nextCursor=heap.toNat ∨ nextCursor=heap.toNat+120) ∧ TableFamily.Model post nextCursor objects := by
  have pools : ∀ index,MemoryModel.PoolFrame source.memory post.memory (objects index).kind (objects index).plan := by
    intro index pool offset inside
    let query := cell (objects index).plan pool offset
    have table := family.tables index
    have number := NaturalLayout.number (objects index).kind (objects index).plan table.valid pool offset inside
    change query.toNat=(objects index).plan.base pool+offset at number
    have lower := table.lower pool
    have earlier := table.earlier pool
    have floorSmall : (objects index).floor<2^64 := by
      have := table.valid.upper pool
      omega
    have bounds := separate index
    have beyond : cursor.toNat≤query.toNat := by omega
    have below : query.toNat<heap.toNat := by omega
    have stateAway := CopyGeneral.Away.before stp query 200 (objects index).floor bounds.2.1 floorSmall (by omega)
    have padAway := CopyGeneral.Away.before pad query 136 (objects index).floor bounds.2.2.1 floorSmall (by omega)
    have nibbleAway := CopyGeneral.Away.before nibs query 64 (objects index).floor bounds.2.2.2 floorSmall (by omega)
    have outputAway := CopyGeneral.Away.after heap query 32 heapAligned (by omega) below
    exact memory query beyond below ⟨stateAway,padAway,outputAway⟩ (by intro offset active; exact (nibbleAway offset active).2)
  rcases result.2 with absent | present
  · refine ⟨heap.toNat,Or.inl rfl,family.advance_pools ?_ (by omega) heapBound heapAligned domain endian pools⟩
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using absent.2
  · have room := present.2.2
    have heapWord : BitVec.ofNat 64 (heap.toNat+120)=heap+120#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),BitVec.toNat_add_of_lt (by change heap.toNat+120<2^64; omega)]
      rfl
    refine ⟨heap.toNat+120,Or.inr rfl,family.advance_pools ?_ (by omega) room (by omega) domain endian pools⟩
    rw [heapWord]
    exact present.2.1

end InitECandidate.Solver.Mpt.WsAccountOptional

#print axioms InitECandidate.Solver.Mpt.WsAccountOptional.Result.family
