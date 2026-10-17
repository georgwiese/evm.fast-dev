import InitECandidate.Solver.WitnessRadix.MemoryBytes

namespace InitECandidate.Solver.WitnessRadix.StoreWord
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def put (memory : BitVec 64 → HolWordLab 64) (address value : BitVec 64) :
    BitVec 64 → HolWordLab 64 :=
  fun current => if current = address then .word value else memory current

theorem execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (destination expression : ExpHOL 64) (address value : BitVec 64)
    (readDestination : QueryBranch.eval source destination = some (.val (.word address)))
    (readValue : QueryBranch.eval source expression = some (.val (.word value)))
    (mapped : source.memaddrs address) :
    evaluateHOLFiniteState source (.store destination expression) =
      (none, { source with memory := put source.memory address value }) := by
  classical
  simp only [QueryBranch.eval] at readDestination readValue
  rw [evaluateHOLFiniteState_store, readDestination]
  simp only [readValue, flattenHOL, panMemStoresHOL, panMemStoreHOL, mapped, ↓reduceIte]
  rfl

theorem byte_away {F : Type} (source : PanSemStateFiniteExact 64 F)
    (address value query : BitVec 64)
    (away : panByteAlignHOL (width := 64) query ≠ address) :
    @panMemLoadByteHOL 64 _ (put source.memory address value) source.memaddrs
      (fun pointer => Classical.propDecidable (source.memaddrs pointer)) source.be query =
    @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun pointer => Classical.propDecidable (source.memaddrs pointer)) source.be query := by
  classical
  simp [panMemLoadByteHOL, put, away]

theorem byteView_away {F : Type} (source : PanSemStateFiniteExact 64 F)
    (address value pointer : BitVec 64) (key : ByteKeys.Key)
    (away : ∀ byte : Fin 32,
      panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 byte.val) ≠ address)
    (view : MemoryBytes.ByteView source pointer key) :
    MemoryBytes.ByteView { source with memory := put source.memory address value } pointer key := by
  intro byte
  rw [byte_away source address value _ (away byte)]
  exact view byte

end InitECandidate.Solver.WitnessRadix.StoreWord

#print axioms InitECandidate.Solver.WitnessRadix.StoreWord.execute
#print axioms InitECandidate.Solver.WitnessRadix.StoreWord.byteView_away
