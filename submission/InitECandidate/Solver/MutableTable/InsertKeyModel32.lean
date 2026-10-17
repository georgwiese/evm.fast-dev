import InitECandidate.Solver.MutableTable.MemoryFrame
import InitECandidate.Solver.WitnessRadix.Copy32Memory

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Actual copying installs the inserted key's bytes and preserves the
represented keys in every other occupied slot. -/
theorem copied_key_views (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters)
    (capacity index : Nat) (table : Find.Model32 (BitVec 64)) (model : Find.KeyModel32 source p capacity table)
    (key : Find.Key32) (value : BitVec 64) (words : Fin 4→BitVec 64)
    (sourceAligned : p.key.toNat%8=0) (sourceFits : p.key.toNat+32<2^64)
    (dstAligned : (p.keys+BitVec.ofNat 64 index*p.stride).toNat%8=0)
    (dstFits : (p.keys+BitVec.ofNat 64 index*p.stride).toNat+32<2^64) (little : source.be=false)
    (sourceWords : MemoryBytes.WordView source p.key words) (sourceBytes : MemoryBytes.ByteView source p.key key)
    (mapped : ∀ limb : Fin 4,source.memaddrs (p.keys+BitVec.ofNat 64 index*p.stride+BitVec.ofNat 64 (8*limb.val)))
    (away : ∀ i<capacity,i≠index→∀ byte : Fin 32,
      panByteAlignHOL (width:=64) (p.keys+BitVec.ofNat 64 i*p.stride+BitVec.ofNat 64 byte.val)∉
        (Copy32.writes (p.keys+BitVec.ofNat 64 index*p.stride) words).map Prod.fst) :
    ∀ i<capacity,∀ storedKey storedValue,Placement.put table index key value i=some (storedKey,storedValue)→
      MemoryBytes.ByteView {source with memory:=Copy32.memory source.memory (p.keys+BitVec.ofNat 64 index*p.stride) words}
        (p.keys+BitVec.ofNat 64 i*p.stride) storedKey := by
  intro i inside storedKey storedValue cell
  by_cases same : i=index
  · subst i
    simp only [Placement.put,if_pos rfl,Option.some.injEq,Prod.mk.injEq] at cell
    obtain ⟨rfl,rfl⟩:=cell
    exact Copy32.byte_view source p.key _ words key sourceAligned dstAligned sourceFits dstFits little sourceWords sourceBytes mapped
  · simp only [Placement.put,if_neg same] at cell
    exact MemoryFrame.byteView_writes_away source _ _ storedKey (away i inside same) (model.view i inside storedKey storedValue cell)

/-- The actual used-byte store activates the chosen slot and preserves all
other flags, including neighbors sharing its physical word. -/
theorem activate_slot (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters)
    (capacity index : Nat) (indexInside : index<capacity) (capacitySmall : capacity≤2^64)
    (table : Find.Model32 (BitVec 64)) (key : Find.Key32) (value : BitVec 64)
    (used : ∀ i<capacity,Find.usedByte source p (BitVec.ofNat 64 i)=
      (match table i with | none=>some 0 | some _=>some 1))
    (views : ∀ i<capacity,∀ storedKey storedValue,Placement.put table index key value i=some (storedKey,storedValue)→
      MemoryBytes.ByteView source (p.keys+BitVec.ofNat 64 i*p.stride) storedKey)
    (little : source.be=false) (mapped : source.memaddrs (panByteAlignHOL (width:=64) (p.used+BitVec.ofNat 64 index)))
    (away : ∀ i<capacity,∀ byte : Fin 32,p.keys+BitVec.ofNat 64 i*p.stride+BitVec.ofNat 64 byte.val≠p.used+BitVec.ofNat 64 index) :
    Find.KeyModel32 {source with memory:=ByteStore.write source.memory (p.used+BitVec.ofNat 64 index) 1} p capacity
      (Placement.put table index key value) := by
  constructor
  · intro i inside
    have read:=ByteStore.read_write source (p.used+BitVec.ofNat 64 index) (p.used+BitVec.ofNat 64 i) 1 little mapped
    change Find.usedByte {source with memory:=ByteStore.write source.memory (p.used+BitVec.ofNat 64 index) 1} p (BitVec.ofNat 64 i)=_ at read
    rw [read]
    by_cases same : i=index
    · subst i;simp [Placement.put]
    · have different : p.used+BitVec.ofNat 64 i≠p.used+BitVec.ofNat 64 index := by
        intro equal
        have words:=(BitVec.add_right_inj p.used).mp equal
        have numbers:=congrArg BitVec.toNat words
        rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at numbers
        exact same numbers
      rw [if_neg different]
      change Find.usedByte source p (BitVec.ofNat 64 i)=_
      rw [used i inside]
      simp only [Placement.put,if_neg same]
      cases table i <;> simp
  · intro i inside storedKey storedValue cell
    exact MemoryFrame.byteView_byte_away source _ _ 1 storedKey little mapped (away i inside)
      (views i inside storedKey storedValue cell)

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.copied_key_views
#print axioms InitECandidate.Solver.MutableTable.Insert.activate_slot
