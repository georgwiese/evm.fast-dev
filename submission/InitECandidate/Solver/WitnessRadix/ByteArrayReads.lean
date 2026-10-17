import InitECandidate.Solver.WitnessRadix.MemoryBytes

namespace InitECandidate.Solver.WitnessRadix.ByteArray
open Flapjack PanSemStateFiniteExact

theorem aligned_cell (pointer : BitVec 64) (offset length : Nat) (inside : offset < length)
    (aligned : pointer.toNat % 8 = 0) (fits : pointer.toNat + length < 2 ^ 64) :
    panByteAlignHOL (width := 64) (byteAddress pointer offset) = byteAddress pointer (8 * (offset / 8)) := by
  have address := byteAddress_toNat pointer offset (by omega)
  have head := byteAddress_toNat pointer (8 * (offset / 8)) (by omega)
  apply BitVec.eq_of_toNat_eq
  change (BitVec.ofNat 64 (((byteAddress pointer offset).toNat / 8) * 8)).toNat = _
  rw [BitVec.toNat_ofNat, address, head, Nat.mod_eq_of_lt (by omega)]
  omega

theorem read_exists {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (length : Nat)
    (mapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress pointer offset))) :
    ∃ bytes : List (BitVec 8), readBytearrayWordHOL (byteWidth := 8) pointer length
      (@panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be) = some bytes ∧ bytes.length = length := by
  classical
  induction length generalizing pointer with
  | zero => exact ⟨[], rfl, rfl⟩
  | succ length ih =>
    have mappedHead : source.memaddrs (panByteAlignHOL (width := 64) pointer) := by
      simpa [byteAddress] using mapped 0 (by omega)
    obtain ⟨rest, tailRead, tailLength⟩ := ih (pointer + 1#64) (by
      intro offset inside
      have next := mapped (1 + offset) (by omega)
      simpa only [byteAddress, BitVec.ofNat_add, BitVec.add_assoc] using next)
    cases cell : source.memory (panByteAlignHOL (width := 64) pointer) with
    | word value =>
      let byte := panGetByteWord8HOL pointer value source.be
      have headRead : @panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs
          (fun address => Classical.propDecidable (source.memaddrs address)) source.be pointer = some byte := by
        simp [panMemLoadByteWord8HOL, mappedHead, cell, byte]
      refine ⟨byte :: rest, ?_, by simp [tailLength]⟩
      rw [readBytearrayWordHOL, headRead]
      exact congrArg (fun result : Option (List (BitVec 8)) => result.bind (fun output => some (byte :: output))) tailRead

theorem read200 {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer : BitVec 64)
    (aligned : pointer.toNat % 8 = 0) (fits : pointer.toNat + 200 < 2 ^ 64)
    (mapped : ∀ word : Fin 25, source.memaddrs (byteAddress pointer (8 * word.val))) :
    ∃ bytes : List (BitVec 8), readBytearrayWordHOL (byteWidth := 8) pointer 200
      (@panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be) = some bytes ∧ bytes.length = 200 := by
  apply read_exists
  intro offset inside
  rw [aligned_cell pointer offset 200 inside aligned fits]
  exact mapped ⟨offset / 8, by omega⟩

end InitECandidate.Solver.WitnessRadix.ByteArray

#print axioms InitECandidate.Solver.WitnessRadix.ByteArray.aligned_cell
#print axioms InitECandidate.Solver.WitnessRadix.ByteArray.read_exists
#print axioms InitECandidate.Solver.WitnessRadix.ByteArray.read200
