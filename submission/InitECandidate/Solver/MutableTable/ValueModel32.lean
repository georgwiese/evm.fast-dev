import InitECandidate.Solver.MutableTable.FindModel32
import InitECandidate.Solver.MutableTable.PlacementUpdate

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack PanSemStateFiniteExact WitnessRadix

def ValueModel32 (source : PanSemStateFiniteExact 64 Guest.HostMemory) (vals : BitVec 64)
    (capacity : Nat) (table : Model32 (BitVec 64)) : Prop :=
  ∀ i<capacity,∀ key value,table i=some (key,value)→
    source.memaddrs (vals+BitVec.ofNat 64 i*8#64) ∧ source.memory (vals+BitVec.ofNat 64 i*8#64)=.word value

theorem value_addresses_distinct (vals : BitVec 64) (capacity i j : Nat)
    (fits : vals.toNat+8*capacity<2^64) (iBound : i<capacity) (jBound : j<capacity) (different : i≠j) :
    vals+BitVec.ofNat 64 i*8#64≠vals+BitVec.ofNat 64 j*8#64 := by
  have first : BitVec.ofNat 64 i*8#64=BitVec.ofNat 64 (8*i):=by rw [Nat.mul_comm 8 i,BitVec.ofNat_mul]
  have second : BitVec.ofNat 64 j*8#64=BitVec.ofNat 64 (8*j):=by rw [Nat.mul_comm 8 j,BitVec.ofNat_mul]
  rw [first,second]
  apply byteAddress_ne vals (8*i) (8*j) (by omega) (by omega) (by omega)

/-- A single real value-cell store implements the represented slot update. -/
theorem value_store_model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (vals : BitVec 64)
    (capacity index : Nat) (inside : index<capacity) (table : Model32 (BitVec 64))
    (model : ValueModel32 source vals capacity table) (key : Key32) (value : BitVec 64)
    (mapped : source.memaddrs (vals+BitVec.ofNat 64 index*8#64)) (fits : vals.toNat+8*capacity<2^64) :
    ValueModel32 {source with memory:=StoreWord.put source.memory (vals+BitVec.ofNat 64 index*8#64) value}
      vals capacity (Placement.put table index key value) := by
  intro i iBound storedKey storedValue cell
  by_cases same : i=index
  · subst i
    simp only [Placement.put,if_pos rfl,Option.some.injEq,Prod.mk.injEq] at cell
    obtain ⟨rfl,rfl⟩:=cell
    exact ⟨mapped,by simp [StoreWord.put]⟩
  · simp only [Placement.put,if_neg same] at cell
    obtain ⟨oldMapped,oldCell⟩:=model i iBound storedKey storedValue cell
    refine ⟨oldMapped,?_⟩
    simpa only [StoreWord.put,if_neg (value_addresses_distinct vals capacity i index fits iBound inside same)] using oldCell

/-- Updating an existing value preserves every used byte and key byte.
The separation premises are physical ownership obligations, not executions. -/
theorem value_store_keys (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters)
    (capacity index : Nat) (table : Model32 (BitVec 64)) (model : KeyModel32 source p capacity table)
    (key : Key32) (old value : BitVec 64) (stored : table index=some (key,old))
    (address : BitVec 64)
    (awayUsed : ∀ i<capacity,panByteAlignHOL (width:=64) (p.used+BitVec.ofNat 64 i)≠address)
    (awayKeys : ∀ i<capacity,∀ byte : Fin 32,
      panByteAlignHOL (width:=64) (p.keys+BitVec.ofNat 64 i*p.stride+BitVec.ofNat 64 byte.val)≠address) :
    KeyModel32 {source with memory:=StoreWord.put source.memory address value} p capacity
      (Placement.put table index key value) := by
  constructor
  · intro i inside
    rw [show usedByte {source with memory:=StoreWord.put source.memory address value} p (BitVec.ofNat 64 i)=
      usedByte source p (BitVec.ofNat 64 i) from StoreWord.byte_away source address value _ (awayUsed i inside),model.used i inside]
    by_cases same : i=index
    · subst i;simp [Placement.put,stored]
    · simp only [Placement.put,if_neg same]
  · intro i inside storedKey storedValue cell
    apply StoreWord.byteView_away source address value _ storedKey (awayKeys i inside)
    by_cases same : i=index
    · subst i
      simp only [Placement.put,if_pos rfl,Option.some.injEq,Prod.mk.injEq] at cell
      obtain ⟨rfl,rfl⟩:=cell
      exact model.view index inside key old stored
    · simp only [Placement.put,if_neg same] at cell
      exact model.view i inside storedKey storedValue cell

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.value_store_model
#print axioms InitECandidate.Solver.MutableTable.Find.value_store_keys
