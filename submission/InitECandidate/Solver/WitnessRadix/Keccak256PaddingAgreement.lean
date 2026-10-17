import InitECandidate.Solver.WitnessRadix.CopyGeneralRegionAgreement
import InitECandidate.Solver.WitnessRadix.ZeroRegionAgreement
import InitECandidate.Solver.WitnessRadix.Keccak256PaddingPrefix

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack PanSemStateFiniteExact MemoryRegion
set_option maxRecDepth 10000

theorem firstPad_memory_agrees {F : Type} (source right : PanSemStateFiniteExact 64 F)
    (endian : source.be = right.be) (region : BitVec 64 → Prop)
    (same : Agree region source.memory right.memory) (scratch rem : BitVec 64) :
    Agree region (firstPadState source scratch rem).memory (firstPadState right scratch rem).memory := by
  simpa only [firstPadState, endian] using
    MemoryRegion.byte_put region source.memory right.memory same right.be (scratch + rem) 1#8

theorem lastPad_memory_agrees {F : Type} (source right : PanSemStateFiniteExact 64 F)
    (endian : source.be = right.be) (region : BitVec 64 → Prop)
    (same : Agree region source.memory right.memory) (scratch : BitVec 64)
    (read : region (panByteAlignHOL (width := 64) (scratch + 135#64))) :
    Agree region (lastPadState source scratch).memory (lastPadState right scratch).memory := by
  have wordEq : lastPadWord source scratch = lastPadWord right scratch := by
    simp only [lastPadWord, ByteRegion.value, endian, same _ read]
  simpa only [lastPadState, endian, wordEq] using
    MemoryRegion.byte_put region source.memory right.memory same right.be (scratch + 135#64)
      (BitVec.ofNat 8 (lastPadWord right scratch).toNat)

/-- Actual zero/copy/first-byte/final-bit padding transformations respect
public memory agreement; private table memory is unrestricted. -/
theorem paddingPrefix_memory_agrees (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (endian : source.be = right.be) (region : BitVec 64 → Prop)
    (same : Agree region source.memory right.memory) (pointer scratch : BitVec 64) (index rem : Nat)
    (wordReads : CopyGeneral.aligned (byteAddress pointer index) scratch →
      ∀ offset < rem, offset % 8 = 0 → region (byteAddress (byteAddress pointer index) offset))
    (byteReads : ∀ offset < rem,
      region (panByteAlignHOL (width := 64) (byteAddress (byteAddress pointer index) offset)))
    (lastRead : region (panByteAlignHOL (width := 64) (scratch + 135#64))) :
    Agree region (paddingPrefixState source pointer scratch index rem).memory
      (paddingPrefixState right pointer scratch index rem).memory := by
  let leftZero := zeroPadState source scratch
  let rightZero := zeroPadState right scratch
  have zeroSame := Zero.finalMemory_agrees region source.memory right.memory same scratch 136
  let leftCopy := CopyGeneral.callState leftZero (byteAddress pointer index) scratch rem
  let rightCopy := CopyGeneral.callState rightZero (byteAddress pointer index) scratch rem
  have copySame : Agree region leftCopy.memory rightCopy.memory := by
    have agreement := CopyGeneral.resultMemory_agrees region leftZero.memory rightZero.memory zeroSame right.be
      (byteAddress pointer index) scratch rem wordReads byteReads
    simpa only [leftCopy, rightCopy, CopyGeneral.callState, leftZero, rightZero, zeroPadState, endian] using agreement
  have firstSame := firstPad_memory_agrees leftCopy rightCopy endian region copySame scratch (BitVec.ofNat 64 rem)
  exact lastPad_memory_agrees (firstPadState leftCopy scratch (BitVec.ofNat 64 rem))
    (firstPadState rightCopy scratch (BitVec.ofNat 64 rem)) endian region firstSame scratch lastRead

theorem paddingPrefix_ffi (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer scratch : BitVec 64) (index rem : Nat) :
    (paddingPrefixState source pointer scratch index rem).ffi = source.ffi := rfl

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.firstPad_memory_agrees
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.lastPad_memory_agrees
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.paddingPrefix_memory_agrees
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.paddingPrefix_ffi
