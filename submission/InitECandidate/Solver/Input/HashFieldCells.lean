import InitECandidate.Solver.Input.HashFields

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes

/-- Exact three physical SI words written by the literal hash-count prefix. -/
theorem hash_fields_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (si np hashes count : BitVec 64)
    (room : si.toNat+96<2^64) :
    (hashFieldsStored source si np hashes count).memory (si+8#64)=.word (np+hashes) ∧
    (hashFieldsStored source si np hashes count).memory (si+16#64)=.word count ∧
    (hashFieldsStored source si np hashes count).memory (si+24#64)=.word (np+8#64) := by
  have first : si+8#64≠si+16#64 := byteAddress_ne si 8 16 (by omega) (by omega) (by decide)
  have second : si+8#64≠si+24#64 := byteAddress_ne si 8 24 (by omega) (by omega) (by decide)
  have third : si+16#64≠si+24#64 := byteAddress_ne si 16 24 (by omega) (by omega) (by decide)
  simp [hashFieldsStored,StructureStore.stored,StoreWord.put,byteAddress,first,second,third]

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.hash_fields_cells
