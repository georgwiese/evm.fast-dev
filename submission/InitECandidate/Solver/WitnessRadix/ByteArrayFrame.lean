import InitECandidate.Solver.WitnessRadix.ByteArrayReads

namespace InitECandidate.Solver.WitnessRadix.ByteArray
open Flapjack PanSemStateFiniteExact

/-- The exact HOL byte-array writer, including its failed-store fallback,
preserves every word outside the aligned cells of its supplied bytes. -/
theorem write_away {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer query : BitVec 64) (bytes : List (BitVec 8))
    (away : ∀ offset < bytes.length, query ≠ panByteAlignHOL (width := 64) (byteAddress pointer offset)) :
    (@panWriteBytearrayWord8HOL 64 _ pointer bytes source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be) query = source.memory query := by
  classical
  induction bytes generalizing pointer with
  | nil => rfl
  | cons byte rest ih =>
    have headAway : query ≠ panByteAlignHOL (width := 64) pointer := by
      simpa [byteAddress] using away 0 (by simp)
    have tailAway := ih (pointer + 1#64) (by
      intro offset inside
      have next := away (1 + offset) (by simp only [List.length_cons]; omega)
      simpa only [byteAddress, BitVec.ofNat_add, BitVec.add_assoc] using next)
    rw [panWriteBytearrayWord8HOL]
    cases stored : (@panWriteBytearrayWord8HOL 64 _ (pointer + 1#64) rest source.memory source.memaddrs
        (fun address => Classical.propDecidable (source.memaddrs address)) source.be) (panByteAlignHOL (width := 64) pointer) with
    | word value =>
      by_cases mapped : source.memaddrs (panByteAlignHOL (width := 64) pointer)
      · simp only [panMemStoreByteWord8HOL, stored, if_pos mapped]
        simp only [if_neg headAway]
        exact tailAway
      · simp only [panMemStoreByteWord8HOL, stored, if_neg mapped]

end InitECandidate.Solver.WitnessRadix.ByteArray

#print axioms InitECandidate.Solver.WitnessRadix.ByteArray.write_away
