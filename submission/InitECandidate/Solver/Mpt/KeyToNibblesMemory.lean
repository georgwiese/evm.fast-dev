import InitECandidate.Solver.Mpt.KeyToNibblesByte
import InitECandidate.Solver.Mpt.TrieWalkMemory

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack PanSemStateFiniteExact
open WitnessRadix WitnessRadix.QueryBranch

theorem pair_other_read {F : Type} (source : PanSemStateFiniteExact 64 F) (out index query : BitVec 64) (offset : Nat) (byte : BitVec 8)
    (little : source.be = false) (firstOther : firstAddress out index offset ≠ query) (secondOther : secondAddress out index offset ≠ query) :
    ByteRegion.read (pairState source out index offset byte) query = ByteRegion.read source query := by
  have faithful : Function.Injective UInt8.ofBitVec := by
    intro left right same
    simpa using congrArg UInt8.toBitVec same
  have actual := pair_other_byte source out index query offset byte little firstOther secondOther
  rw [panMemLoadByteHOL_eq_word8_projection, panMemLoadByteHOL_eq_word8_projection] at actual
  have exactRead := Option.map_injective faithful actual
  change @panMemLoadByteWord8HOL 64 _ (pairState source out index offset byte).memory source.memaddrs
    (fun address => Classical.propDecidable (source.memaddrs address)) source.be query =
    @panMemLoadByteWord8HOL 64 _ source.memory source.memaddrs (fun address => Classical.propDecidable (source.memaddrs address)) source.be query
  rwa [little]

theorem pair_preserves_input {F : Type} (source : PanSemStateFiniteExact 64 F) (key out index : BitVec 64)
    (length offset : Nat) (byte : BitVec 8) (bytes : Nat → BitVec 8)
    (little : source.be = false) (reads : ByteRegion.Reads source key length bytes)
    (firstOther : ∀ position < length, firstAddress out index offset ≠ byteAddress key position)
    (secondOther : ∀ position < length, secondAddress out index offset ≠ byteAddress key position) :
    ByteRegion.Reads (pairState source out index offset byte) key length bytes := by
  intro position inside
  rw [pair_other_read source out index _ offset byte little (firstOther position inside) (secondOther position inside)]
  exact reads position inside

def NibblePrefix {F : Type} (source : PanSemStateFiniteExact 64 F) (out : BitVec 64) (count : Nat) : Prop :=
  ∀ offset < count, ∃ byte : UInt8, byte.toNat < 16 ∧
    @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address => Classical.propDecidable (source.memaddrs address))
      source.be (byteAddress out offset) = some byte

theorem pair_addresses (out : BitVec 64) (index offset : Nat) :
    firstAddress out (BitVec.ofNat 64 index) offset = byteAddress out (2 * (index + offset)) ∧
    secondAddress out (BitVec.ofNat 64 index) offset = byteAddress out (2 * (index + offset) + 1) := by
  have product : 2#64 * BitVec.ofNat 64 index = BitVec.ofNat 64 (2 * index) := by rw [BitVec.ofNat_mul]
  constructor
  all_goals
    simp only [firstAddress, secondAddress, byteAddress, product, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2 <;> omega

theorem output_address_different (out : BitVec 64) (left right : Nat)
    (fits : out.toNat + 64 < 2^64) (leftInside : left < 64) (rightInside : right < 64) (different : left ≠ right) :
    byteAddress out left ≠ byteAddress out right := by
  intro same
  have numbers := congrArg BitVec.toNat same
  rw [byteAddress_toNat out left (by omega), byteAddress_toNat out right (by omega)] at numbers
  omega

/-- Two real stores extend the verified nibble prefix while preserving
all earlier bytes, including earlier bytes in the same backing word. -/
theorem NibblePrefix.pair {F : Type} (source : PanSemStateFiniteExact 64 F) (out : BitVec 64) (index offset : Nat) (byte : BitVec 8)
    (little : source.be = false) (fits : out.toNat + 64 < 2^64) (room : 2 * (index + offset) + 2 ≤ 64)
    (prior : NibblePrefix source out (2 * (index + offset)))
    (firstMapped : source.memaddrs (panByteAlignHOL (width := 64) (firstAddress out (BitVec.ofNat 64 index) offset)))
    (secondMapped : source.memaddrs (panByteAlignHOL (width := 64) (secondAddress out (BitVec.ofNat 64 index) offset))) :
    NibblePrefix (pairState source out (BitVec.ofNat 64 index) offset byte) out (2 * (index + offset) + 2) := by
  intro position inside
  have addresses := pair_addresses out index offset
  have reads := pair_reads source out (BitVec.ofNat 64 index) offset byte little firstMapped secondMapped
  rw [addresses.1, addresses.2] at reads
  by_cases earlier : position < 2 * (index + offset)
  · obtain ⟨value, small, read⟩ := prior position earlier
    have otherFirst : firstAddress out (BitVec.ofNat 64 index) offset ≠ byteAddress out position := by
      rw [addresses.1]
      exact output_address_different out _ _ fits (by omega) (by omega) (by omega)
    have otherSecond : secondAddress out (BitVec.ofNat 64 index) offset ≠ byteAddress out position := by
      rw [addresses.2]
      exact output_address_different out _ _ fits (by omega) (by omega) (by omega)
    have retained := pair_other_byte source out (BitVec.ofNat 64 index) (byteAddress out position) offset byte little otherFirst otherSecond
    refine ⟨value, small, ?_⟩
    change @panMemLoadByteHOL 64 _ (pairState source out (BitVec.ofNat 64 index) offset byte).memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be (byteAddress out position) = _
    rw [little, retained]
    rwa [little] at read
  · have cases : position = 2 * (index + offset) ∨ position = 2 * (index + offset) + 1 := by omega
    rcases cases with rfl | rfl
    · refine ⟨UInt8.ofNat (high byte).toNat, ?_, ?_⟩
      · rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by have small := high_small byte; omega)]
        exact high_small byte
      · change @panMemLoadByteHOL 64 _ (pairState source out (BitVec.ofNat 64 index) offset byte).memory source.memaddrs
          (fun address => Classical.propDecidable (source.memaddrs address)) source.be _ = _
        rw [little]
        exact reads.1
    · refine ⟨UInt8.ofNat (low byte).toNat, ?_, ?_⟩
      · rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by have small := low_small byte; omega)]
        exact low_small byte
      · change @panMemLoadByteHOL 64 _ (pairState source out (BitVec.ofNat 64 index) offset byte).memory source.memaddrs
          (fun address => Classical.propDecidable (source.memaddrs address)) source.be _ = _
        rw [little]
        exact reads.2

theorem NibblePrefix.key_view (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out : BitVec 64)
    (fits : out.toNat + 64 < 2^64)
    (mapped : ∀ offset < 64, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress out offset)))
    (nibbles : NibblePrefix source out 64) : TrieWalk.KeyView source.memory source.memaddrs source.be out 64 :=
  ⟨by decide, fits, mapped, nibbles⟩

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.pair_other_read
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.pair_preserves_input
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.pair_addresses
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.output_address_different
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.NibblePrefix.pair
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.NibblePrefix.key_view
