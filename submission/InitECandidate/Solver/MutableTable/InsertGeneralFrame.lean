import InitECandidate.Solver.MutableTable.InsertGeneralTail

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Complete untouched-word frame of the actual arbitrary-width insertion
memory. Each premise is a physical copy/store separation fact. -/
theorem general_result_away (memory : WordWrites.Memory) (be : Bool) (width : Nat) (p : Find.Parameters)
    (table vals order position index count value query : BitVec 64)
    (copyAway : CopyGeneral.Away (p.keys + index * p.stride) query width)
    (valueAway : query ≠ vals + index * 8#64)
    (usedAway : query ≠ panByteAlignHOL (width := 64) (p.used + index))
    (metaAway : query ∉ (countWrites table order position index count).map Prod.fst) :
    generalResultMemory memory be width p table vals order position index count value query = memory query := by
  rw [generalResultMemory, suffixMemory, WordWrites.write_away _ _ _ metaAway]
  simp only [ByteStore.write, StoreWord.put, if_neg usedAway, if_neg valueAway]
  exact CopyGeneral.resultMemory_away memory be p.key (p.keys + index * p.stride) query width copyAway

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.general_result_away
