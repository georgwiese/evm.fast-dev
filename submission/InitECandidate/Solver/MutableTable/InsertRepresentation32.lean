import InitECandidate.Solver.MutableTable.InsertKeyModel32
import InitECandidate.Solver.MutableTable.InsertValueModel32

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The complete actual insertion-memory formula represents the updated
keys and used bytes. All physical separation obligations are explicit. -/
theorem result_keys (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters)
    (capacity index : Nat) (inside : index<capacity) (capacitySmall : capacity≤2^64)
    (logical : Find.Model32 (BitVec 64)) (model : Find.KeyModel32 source p capacity logical)
    (table vals order position count value : BitVec 64) (key : Find.Key32) (words : Fin 4→BitVec 64)
    (sourceAligned : p.key.toNat%8=0) (sourceFits : p.key.toNat+32<2^64)
    (dstAligned : (p.keys+BitVec.ofNat 64 index*p.stride).toNat%8=0)
    (dstFits : (p.keys+BitVec.ofNat 64 index*p.stride).toNat+32<2^64) (little : source.be=false)
    (sourceWords : MemoryBytes.WordView source p.key words) (sourceBytes : MemoryBytes.ByteView source p.key key)
    (copyMapped : ∀ limb : Fin 4,source.memaddrs (p.keys+BitVec.ofNat 64 index*p.stride+BitVec.ofNat 64 (8*limb.val)))
    (usedMapped : source.memaddrs (panByteAlignHOL (width:=64) (p.used+BitVec.ofNat 64 index)))
    (copyUsedAway : ∀ i<capacity,panByteAlignHOL (width:=64) (p.used+BitVec.ofNat 64 i)∉
      (Copy32.writes (p.keys+BitVec.ofNat 64 index*p.stride) words).map Prod.fst)
    (copyKeysAway : ∀ i<capacity,i≠index→∀ byte : Fin 32,
      panByteAlignHOL (width:=64) (p.keys+BitVec.ofNat 64 i*p.stride+BitVec.ofNat 64 byte.val)∉
      (Copy32.writes (p.keys+BitVec.ofNat 64 index*p.stride) words).map Prod.fst)
    (valueUsedAway : ∀ i<capacity,panByteAlignHOL (width:=64) (p.used+BitVec.ofNat 64 i)≠vals+BitVec.ofNat 64 index*8#64)
    (valueKeysAway : ∀ i<capacity,∀ byte : Fin 32,
      panByteAlignHOL (width:=64) (p.keys+BitVec.ofNat 64 i*p.stride+BitVec.ofNat 64 byte.val)≠vals+BitVec.ofNat 64 index*8#64)
    (usedKeysAway : ∀ i<capacity,∀ byte : Fin 32,
      p.keys+BitVec.ofNat 64 i*p.stride+BitVec.ofNat 64 byte.val≠p.used+BitVec.ofNat 64 index)
    (metaUsedAway : ∀ i<capacity,panByteAlignHOL (width:=64) (p.used+BitVec.ofNat 64 i)∉
      (countWrites table order position (BitVec.ofNat 64 index) count).map Prod.fst)
    (metaKeysAway : ∀ i<capacity,∀ byte : Fin 32,
      panByteAlignHOL (width:=64) (p.keys+BitVec.ofNat 64 i*p.stride+BitVec.ofNat 64 byte.val)∉
      (countWrites table order position (BitVec.ofNat 64 index) count).map Prod.fst) :
    Find.KeyModel32 {source with memory:=resultMemory source.memory p table vals order position (BitVec.ofNat 64 index) count value words}
      p capacity (Placement.put logical index key value) := by
  let copied:={source with memory:=Copy32.memory source.memory (p.keys+BitVec.ofNat 64 index*p.stride) words}
  let valued:={copied with memory:=StoreWord.put copied.memory (vals+BitVec.ofNat 64 index*8#64) value}
  let flagged:={valued with memory:=ByteStore.write valued.memory (p.used+BitVec.ofNat 64 index) 1}
  have copiedUsed (i : Nat) (iBound : i<capacity) : Find.usedByte copied p (BitVec.ofNat 64 i)=
      (match logical i with | none=>some 0 | some _=>some 1) := by
    have same : Find.usedByte copied p (BitVec.ofNat 64 i)=Find.usedByte source p (BitVec.ofNat 64 i):=
      MemoryFrame.byte_writes_away source _ _ (copyUsedAway i iBound)
    rw [same,model.used i iBound]
    cases logical i <;> simp
  have copiedViews:=copied_key_views source p capacity index logical model key value words sourceAligned sourceFits dstAligned dstFits
    little sourceWords sourceBytes copyMapped copyKeysAway
  have valuedUsed (i : Nat) (iBound : i<capacity) : Find.usedByte valued p (BitVec.ofNat 64 i)=
      (match logical i with | none=>some 0 | some _=>some 1) :=
    (StoreWord.byte_away copied _ value _ (valueUsedAway i iBound)).trans (copiedUsed i iBound)
  have valuedViews (i : Nat) (iBound : i<capacity) (storedKey : Find.Key32) (storedValue : BitVec 64)
      (cell : Placement.put logical index key value i=some (storedKey,storedValue)) :
      MemoryBytes.ByteView valued (p.keys+BitVec.ofNat 64 i*p.stride) storedKey :=
    StoreWord.byteView_away copied _ value _ storedKey (valueKeysAway i iBound) (copiedViews i iBound storedKey storedValue cell)
  have activated : Find.KeyModel32 flagged p capacity (Placement.put logical index key value):=
    activate_slot valued p capacity index inside capacitySmall logical key value valuedUsed valuedViews little usedMapped usedKeysAway
  exact MemoryFrame.keys_writes_away flagged _ p capacity (Placement.put logical index key value) metaUsedAway metaKeysAway activated

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.result_keys
