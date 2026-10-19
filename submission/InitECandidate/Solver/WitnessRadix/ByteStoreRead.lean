import InitECandidate.Solver.WitnessRadix.ByteStore

namespace InitECandidate.Solver.WitnessRadix.ByteStore
open Flapjack PanSemStateFiniteExact

theorem get_set_self (address word : BitVec 64) (byte : BitVec 8) :
    (panGetByteHOL address (panSetByteHOL address (BitVec.ofNat 64 byte.toNat) word false) false).toNat = byte.toNat := by
  have byteSmall := byte.isLt
  have wordSmall := word.isLt
  have residue : address.toNat % 8 = 0 ∨ address.toNat % 8 = 1 ∨ address.toNat % 8 = 2 ∨
      address.toNat % 8 = 3 ∨ address.toNat % 8 = 4 ∨ address.toNat % 8 = 5 ∨
      address.toNat % 8 = 6 ∨ address.toNat % 8 = 7 := by omega
  rcases residue with h | h | h | h | h | h | h | h
  all_goals
    simp [panGetByteHOL, panSetByteHOL, h, BitVec.toNat_ofNat, UInt8.toNat_ofNat']
    omega

theorem read_self (memory : WordWrites.Memory) (domain : BitVec 64 → Prop) (address : BitVec 64) (byte : BitVec 8)
    (mapped : domain (panByteAlignHOL (width := 64) address)) :
    @panMemLoadByteHOL 64 _ (put memory false address byte) domain (fun query => Classical.propDecidable (domain query)) false address =
      some (UInt8.ofNat byte.toNat) := by
  have projected := get_set_self address (MemoryBytes.wordBits (memory (panByteAlignHOL (width := 64) address))) byte
  have equal : panGetByteHOL address (panSetByteHOL address (BitVec.ofNat 64 byte.toNat)
      (MemoryBytes.wordBits (memory (panByteAlignHOL (width := 64) address))) false) false = UInt8.ofNat byte.toNat := by
    apply UInt8.toNat.inj
    rw [projected, UInt8.toNat_ofNat', Nat.mod_eq_of_lt byte.isLt]
  simp only [panMemLoadByteHOL, put, StoreWord.put, ↓reduceIte, mapped, equal]

theorem get_set_other (address query word : BitVec 64) (byte : BitVec 8)
    (different : address.toNat % 8 ≠ query.toNat % 8) :
    panGetByteHOL query (panSetByteHOL address (BitVec.ofNat 64 byte.toNat) word false) false =
      panGetByteHOL query word false := by
  apply UInt8.toNat.inj
  have byteSmall := byte.isLt
  have wordSmall := word.isLt
  have written : address.toNat % 8 = 0 ∨ address.toNat % 8 = 1 ∨ address.toNat % 8 = 2 ∨
      address.toNat % 8 = 3 ∨ address.toNat % 8 = 4 ∨ address.toNat % 8 = 5 ∨
      address.toNat % 8 = 6 ∨ address.toNat % 8 = 7 := by omega
  have observed : query.toNat % 8 = 0 ∨ query.toNat % 8 = 1 ∨ query.toNat % 8 = 2 ∨
      query.toNat % 8 = 3 ∨ query.toNat % 8 = 4 ∨ query.toNat % 8 = 5 ∨
      query.toNat % 8 = 6 ∨ query.toNat % 8 = 7 := by omega
  rcases written with h | h | h | h | h | h | h | h
  all_goals rcases observed with k | k | k | k | k | k | k | k
  all_goals simp only [h, k] at different
  all_goals first
    | exact (different rfl).elim
    | (simp [panGetByteHOL, panSetByteHOL, h, k, BitVec.toNat_ofNat, UInt8.toNat_ofNat']; omega)

theorem read_other (memory : WordWrites.Memory) (domain : BitVec 64 → Prop) (address query : BitVec 64) (byte : BitVec 8)
    (different : address ≠ query) :
    @panMemLoadByteHOL 64 _ (put memory false address byte) domain (fun cell => Classical.propDecidable (domain cell)) false query =
      @panMemLoadByteHOL 64 _ memory domain (fun cell => Classical.propDecidable (domain cell)) false query := by
  by_cases same : panByteAlignHOL (width := 64) query = panByteAlignHOL (width := 64) address
  · have residues : address.toNat % 8 ≠ query.toNat % 8 := by
      intro equal
      apply different
      apply BitVec.eq_of_toNat_eq
      have aligned := congrArg BitVec.toNat same
      have aSmall := address.isLt
      have qSmall := query.isLt
      have aBound : address.toNat / 8 * 8 < 2^64 := by omega
      have qBound : query.toNat / 8 * 8 < 2^64 := by omega
      change (BitVec.ofNat 64 (query.toNat / 8 * 8)).toNat = (BitVec.ofNat 64 (address.toNat / 8 * 8)).toNat at aligned
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt aBound, Nat.mod_eq_of_lt qBound] at aligned
      omega
    cases cell : memory (panByteAlignHOL (width := 64) address) with
    | word word =>
      have preserved := get_set_other address query word byte residues
      by_cases mapped : domain (panByteAlignHOL (width := 64) address)
      all_goals simp only [panMemLoadByteHOL, put, StoreWord.put, same, ↓reduceIte, cell, MemoryBytes.wordBits, mapped, preserved]
  · simp only [panMemLoadByteHOL, put, StoreWord.put, if_neg same]

end InitECandidate.Solver.WitnessRadix.ByteStore

#print axioms InitECandidate.Solver.WitnessRadix.ByteStore.get_set_self
#print axioms InitECandidate.Solver.WitnessRadix.ByteStore.read_self
#print axioms InitECandidate.Solver.WitnessRadix.ByteStore.get_set_other
#print axioms InitECandidate.Solver.WitnessRadix.ByteStore.read_other
