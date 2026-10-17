import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.WitnessRadix.MemoryBytes
open Flapjack PanSemStateFiniteExact

/-- A byte load depends on its aligned word, mapping and endianness only. -/
theorem read_of_cell {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be) (address : BitVec 64)
    (word : source.memory (panByteAlignHOL (width := 64) address) =
      target.memory (panByteAlignHOL (width := 64) address)) :
    @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun pointer => Classical.propDecidable (source.memaddrs pointer)) source.be address =
    @panMemLoadByteHOL 64 _ target.memory target.memaddrs
      (fun pointer => Classical.propDecidable (target.memaddrs pointer)) target.be address := by
  classical
  by_cases mapped : target.memaddrs (panByteAlignHOL (width := 64) address)
  all_goals simp [panMemLoadByteHOL, domain, endian, word, mapped]

theorem byteView_of_cells {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be)
    (pointer : BitVec 64) (key : ByteKeys.Key)
    (words : ∀ byte : Fin 32,
      source.memory (panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 byte.val)) =
      target.memory (panByteAlignHOL (width := 64) (pointer + BitVec.ofNat 64 byte.val)))
    (view : ByteView source pointer key) : ByteView target pointer key := by
  intro byte
  rw [← read_of_cell source target domain endian _ (words byte)]
  exact view byte

end InitECandidate.Solver.WitnessRadix.MemoryBytes

#print axioms InitECandidate.Solver.WitnessRadix.MemoryBytes.read_of_cell
#print axioms InitECandidate.Solver.WitnessRadix.MemoryBytes.byteView_of_cells
