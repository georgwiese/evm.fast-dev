import InitECandidate.Solver.WitnessRadix.ByteStore

namespace InitECandidate.Solver.WitnessRadix.ByteStore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem execute_word {F : Type} (source : PanSemStateFiniteExact 64 F) (destination expression : ExpHOL 64)
    (address value : BitVec 64)
    (readAddress : QueryBranch.eval source destination=some (.val (.word address)))
    (readValue : QueryBranch.eval source expression=some (.val (.word value)))
    (mapped : source.memaddrs (panByteAlignHOL (width := 64) address)) :
    evaluateHOLFiniteState source (.storeByte destination expression)=
      (none,{source with memory := put source.memory source.be address (BitVec.ofNat 8 value.toNat)}) := by
  classical
  simp only [QueryBranch.eval] at readAddress readValue
  rw [evaluateHOLFiniteState_storeByte,readAddress,readValue]
  cases stored : source.memory (panByteAlignHOL (width := 64) address) with
  | word word =>
    simp [panMemStoreByteWord8HOL,mapped,stored,put,MemoryBytes.wordBits,StoreWord.put]
    rfl

end InitECandidate.Solver.WitnessRadix.ByteStore

#print axioms InitECandidate.Solver.WitnessRadix.ByteStore.execute_word
