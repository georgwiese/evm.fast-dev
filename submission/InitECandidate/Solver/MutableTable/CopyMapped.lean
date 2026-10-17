import InitECandidate.Solver.WitnessRadix.CopyGeneralCall
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.AlignedMapped

namespace InitECandidate.Solver.MutableTable.CopyMapped
open Flapjack PanSemStateFiniteExact
open WitnessRadix

/-- A byte-region mapping derives every actual aligned memcpy word mapping,
including partial final words; no successful-copy premise is used. -/
theorem word_mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (length offset : Nat)
    (aligned : pointer &&& 7#64 = 0#64) (fits : pointer.toNat + length < 2 ^ 64)
    (mapped : ∀ byte < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress pointer byte)))
    (inside : offset < length) (multiple : offset % 8 = 0) : source.memaddrs (byteAddress pointer offset) := by
  have pointerAligned : pointer.toNat % 8 = 0 := by rw [← WordBits.mask7 pointer, aligned]; rfl
  have addressNumber := byteAddress_toNat pointer offset (by omega)
  have alignEq : panByteAlignHOL (width := 64) (byteAddress pointer offset) = byteAddress pointer offset := by
    apply BitVec.eq_of_toNat_eq
    rw [InitECandidate.Solver.MutableTable.ByteStore.aligned_number, addressNumber]
    omega
  have actual := mapped offset inside
  rw [alignEq] at actual
  exact actual

theorem of_regions {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat)
    (srcFits : src.toNat + length < 2 ^ 64) (dstFits : dst.toNat + length < 2 ^ 64)
    (sourceBytes : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress src offset)))
    (destinationBytes : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress dst offset))) :
    CopyContext.Mapped source src dst length := by
  refine ⟨sourceBytes, destinationBytes, ?_, ?_⟩
  · intro aligned offset inside multiple
    have both : dst &&& 7#64 = 0#64 ∧ src &&& 7#64 = 0#64 := by
      rw [BitVec.and_or_distrib_right, BitVec.or_eq_zero_iff] at aligned
      exact aligned
    exact word_mapped source src length offset both.2 srcFits sourceBytes inside multiple
  · intro aligned offset inside multiple
    have both : dst &&& 7#64 = 0#64 ∧ src &&& 7#64 = 0#64 := by
      rw [BitVec.and_or_distrib_right, BitVec.or_eq_zero_iff] at aligned
      exact aligned
    exact word_mapped source dst length offset both.1 dstFits destinationBytes inside multiple

/-- Uniform byte-loop allowance dominates the original faster aligned copy
loops. This is a source-clock bound and omits straight-line copying work. -/
theorem cost_le_price (src dst : BitVec 64) (length : Nat) : CopyGeneral.cost src dst length ≤ MemeqByteRuntime.price length := by
  unfold CopyGeneral.cost
  split <;> dsimp [CopyWords.prefixCost, CopyWords.prefixIndex, CopyBytes.suffixCost, MemeqByteRuntime.price] <;> omega

end InitECandidate.Solver.MutableTable.CopyMapped

#print axioms InitECandidate.Solver.MutableTable.CopyMapped.word_mapped
#print axioms InitECandidate.Solver.MutableTable.CopyMapped.of_regions
#print axioms InitECandidate.Solver.MutableTable.CopyMapped.cost_le_price
