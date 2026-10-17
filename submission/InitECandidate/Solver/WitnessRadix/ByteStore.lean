import InitECandidate.Solver.WitnessRadix.ZeroByteStore

namespace InitECandidate.Solver.WitnessRadix.ByteStore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def put (memory : WordWrites.Memory) (be : Bool) (address : BitVec 64) (value : BitVec 8) : WordWrites.Memory :=
  StoreWord.put memory (panByteAlignHOL (width := 64) address)
    (panSetByteHOL address (BitVec.ofNat 64 value.toNat)
      (MemoryBytes.wordBits (memory (panByteAlignHOL (width := 64) address))) be)

/-- An actual ordinary byte store writes exactly its aligned word; the
stored byte is the real evaluated value, without an assumed copy oracle. -/
theorem execute {F : Type} (source : PanSemStateFiniteExact 64 F) (destination expression : ExpHOL 64)
    (address : BitVec 64) (value : BitVec 8)
    (readAddress : QueryBranch.eval source destination = some (.val (.word address)))
    (readValue : QueryBranch.eval source expression = some (.val (.word (BitVec.ofNat 64 value.toNat))))
    (mapped : source.memaddrs (panByteAlignHOL (width := 64) address)) :
    evaluateHOLFiniteState source (.storeByte destination expression) =
      (none, { source with memory := put source.memory source.be address value }) := by
  classical
  simp only [QueryBranch.eval] at readAddress readValue
  rw [evaluateHOLFiniteState_storeByte, readAddress, readValue]
  simp only []
  have small : value.toNat < 2 ^ 64 := by have := value.isLt; omega
  have widened : (BitVec.ofNat 64 value.toNat).toNat = value.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  have narrowed : BitVec.ofNat 8 value.toNat = value := by simp
  rw [widened, narrowed]
  cases stored : source.memory (panByteAlignHOL (width := 64) address) with
  | word word =>
    simp [panMemStoreByteWord8HOL, mapped, stored, put, MemoryBytes.wordBits, StoreWord.put]
    rfl

theorem away (memory : WordWrites.Memory) (be : Bool) (address query : BitVec 64) (value : BitVec 8)
    (different : query ≠ panByteAlignHOL (width := 64) address) : put memory be address value query = memory query :=
  if_neg different

end InitECandidate.Solver.WitnessRadix.ByteStore

#print axioms InitECandidate.Solver.WitnessRadix.ByteStore.execute
#print axioms InitECandidate.Solver.WitnessRadix.ByteStore.away
