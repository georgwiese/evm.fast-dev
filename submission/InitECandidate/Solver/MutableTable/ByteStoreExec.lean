import InitECandidate.Solver.MutableTable.ByteStore

namespace InitECandidate.Solver.MutableTable.ByteStore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

/-- Exact state change of a mapped little-endian source byte store. -/
theorem execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (destination expression : ExpHOL 64) (address : BitVec 64) (byte : UInt8)
    (readDestination : QueryBranch.eval source destination=some (.val (.word address)))
    (readValue : QueryBranch.eval source expression=some (.val (.word (BitVec.ofNat 64 byte.toNat))))
    (mapped : source.memaddrs (panByteAlignHOL (width:=64) address)) (little : source.be=false) :
    evaluateHOLFiniteState source (.storeByte destination expression)=
      (none,{source with memory:=write source.memory address byte}) := by
  classical
  simp only [QueryBranch.eval] at readDestination readValue
  rw [evaluateHOLFiniteState_storeByte,readDestination,readValue]
  cases stored : source.memory (panByteAlignHOL (width:=64) address) with
  | word value=>
    simp [panMemStoreByteWord8HOL,mapped,stored,little,write,MemoryBytes.wordBits,StoreWord.put]
    rfl

end InitECandidate.Solver.MutableTable.ByteStore

#print axioms InitECandidate.Solver.MutableTable.ByteStore.execute
