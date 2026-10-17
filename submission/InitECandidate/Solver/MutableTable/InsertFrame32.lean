import InitECandidate.Solver.MutableTable.InsertRepresentation32

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Complete untouched-word frame of the actual insertion-memory formula. -/
theorem result_away (memory : WordWrites.Memory) (p : Find.Parameters)
    (table vals order position index count value query : BitVec 64) (words : Fin 4→BitVec 64)
    (copyAway : query∉(Copy32.writes (p.keys+index*p.stride) words).map Prod.fst)
    (valueAway : query≠vals+index*8#64) (usedAway : query≠panByteAlignHOL (width:=64) (p.used+index))
    (metaAway : query∉(countWrites table order position index count).map Prod.fst) :
    resultMemory memory p table vals order position index count value words query=memory query := by
  rw [resultMemory,suffixMemory,WordWrites.write_away _ _ _ metaAway]
  simp only [ByteStore.write,StoreWord.put,if_neg usedAway,if_neg valueAway]
  exact WordWrites.write_away memory _ query copyAway

/-- Insertion preserves the complete original find/get physical header when
the inserted arrays and metadata cells are separated from its header fields. -/
theorem result_header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Find.Parameters)
    (table vals order position index count value : BitVec 64) (words : Fin 4→BitVec 64)
    (header : Find.HeaderData source table p)
    (copyAway : ∀ offset∈([0,8,16,32,48] : List Nat),
      table+BitVec.ofNat 64 offset∉(Copy32.writes (p.keys+index*p.stride) words).map Prod.fst)
    (valueAway : ∀ offset∈([0,8,16,32,48] : List Nat),table+BitVec.ofNat 64 offset≠vals+index*8#64)
    (usedAway : ∀ offset∈([0,8,16,32,48] : List Nat),
      table+BitVec.ofNat 64 offset≠panByteAlignHOL (width:=64) (p.used+index))
    (metaAway : ∀ offset∈([0,8,16,32,48] : List Nat),
      table+BitVec.ofNat 64 offset∉(countWrites table order position index count).map Prod.fst) :
    Find.HeaderData {source with memory:=resultMemory source.memory p table vals order position index count value words} table p := by
  have frame (offset : Nat) (member : offset∈([0,8,16,32,48] : List Nat)) :=
    result_away source.memory p table vals order position index count value (table+BitVec.ofNat 64 offset) words
      (copyAway offset member) (valueAway offset member) (usedAway offset member) (metaAway offset member)
  refine ⟨header.mapped,?_,?_,?_,?_,?_⟩
  · exact (frame 16 (by simp)).trans header.capacity
  · simpa only [BitVec.add_zero] using (frame 0 (by simp)).trans (show source.memory (table+0#64)=.word p.keyLength by simpa using header.keyLength)
  · exact (frame 8 (by simp)).trans header.stride
  · exact (frame 32 (by simp)).trans header.keys
  · exact (frame 48 (by simp)).trans header.used

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.result_away
#print axioms InitECandidate.Solver.MutableTable.Insert.result_header
