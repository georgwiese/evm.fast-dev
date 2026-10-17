import InitECandidate.Solver.MutableTable.InsertTail32
import InitECandidate.Solver.MutableTable.MemoryFrame

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Final insertion memory stores the exact incremented count. This is the
last metadata write, so earlier aliasing does not weaken this readback fact. -/
theorem result_count (memory : WordWrites.Memory) (p : Find.Parameters) (table vals order position index count value : BitVec 64)
    (words : Fin 4→BitVec 64) :
    resultMemory memory p table vals order position index count value words (table+24#64)=.word (count+1#64) := by
  simp [resultMemory,suffixMemory,countWrites,WordWrites.write,StoreWord.put]

/-- All actual insertion stores establish and preserve the represented
values. Separation is stated at the physical cells that must be owned. -/
theorem result_values (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters)
    (capacity index : Nat) (inside : index<capacity) (logical : Find.Model32 (BitVec 64))
    (table vals order position count value : BitVec 64) (key : Find.Key32) (words : Fin 4→BitVec 64)
    (model : Find.ValueModel32 source vals capacity logical)
    (fits : vals.toNat+8*capacity<2^64) (mapped : source.memaddrs (vals+BitVec.ofNat 64 index*8#64))
    (copyAway : ∀ i<capacity,vals+BitVec.ofNat 64 i*8#64∉
      (Copy32.writes (p.keys+BitVec.ofNat 64 index*p.stride) words).map Prod.fst)
    (usedAway : ∀ i<capacity,vals+BitVec.ofNat 64 i*8#64≠panByteAlignHOL (width:=64) (p.used+BitVec.ofNat 64 index))
    (metaAway : ∀ i<capacity,vals+BitVec.ofNat 64 i*8#64∉
      (countWrites table order position (BitVec.ofNat 64 index) count).map Prod.fst) :
    Find.ValueModel32 {source with memory:=resultMemory source.memory p table vals order position (BitVec.ofNat 64 index) count value words}
      vals capacity (Placement.put logical index key value) := by
  let copied:={source with memory:=Copy32.memory source.memory (p.keys+BitVec.ofNat 64 index*p.stride) words}
  let valued:={copied with memory:=StoreWord.put copied.memory (vals+BitVec.ofNat 64 index*8#64) value}
  let flagged:={valued with memory:=ByteStore.write valued.memory (p.used+BitVec.ofNat 64 index) 1}
  have copyModel : Find.ValueModel32 copied vals capacity logical:=MemoryFrame.values_writes_away source _ vals capacity logical copyAway model
  have valueModel : Find.ValueModel32 valued vals capacity (Placement.put logical index key value):=
    Find.value_store_model copied vals capacity index inside logical copyModel key value mapped fits
  have flaggedModel : Find.ValueModel32 flagged vals capacity (Placement.put logical index key value) := by
    intro i iBound storedKey storedValue cell
    obtain ⟨mapped,stored⟩:=valueModel i iBound storedKey storedValue cell
    refine ⟨mapped,?_⟩
    simpa only [flagged,ByteStore.write,StoreWord.put,if_neg (usedAway i iBound)] using stored
  exact MemoryFrame.values_writes_away flagged _ vals capacity (Placement.put logical index key value) metaAway flaggedModel

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.result_count
#print axioms InitECandidate.Solver.MutableTable.Insert.result_values
