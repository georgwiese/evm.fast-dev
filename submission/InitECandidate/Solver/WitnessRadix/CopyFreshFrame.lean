import InitECandidate.Solver.WitnessRadix.CopyGeneralMemoryResult
import InitECandidate.Solver.WitnessRadix.CopyAwayIntervals

namespace InitECandidate.Solver.WitnessRadix.CopyGeneral
open Flapjack PanSemStateFiniteExact

/-- A fresh destination may be unaligned, but every byte backing word
still follows an aligned older frontier. -/
theorem Away.after_floor (pointer query : BitVec 64) (length lower : Nat)
    (aligned : lower%8=0) (above : lower≤pointer.toNat) (fits : pointer.toNat+length<2^64) (before : query.toNat<lower) : Away pointer query length := by
  intro offset inside
  have number:=byteAddress_toNat pointer offset (by omega)
  have backing:=AllocatedBytes.aligned_number (byteAddress pointer offset)
  constructor
  · intro equal
    have same:=congrArg BitVec.toNat equal
    omega
  · intro equal
    have same:=congrArg BitVec.toNat equal
    rw [backing,number] at same
    omega

theorem result_before_floor (memory : WordWrites.Memory) (be : Bool) (src dst query : BitVec 64) (length lower : Nat)
    (aligned : lower%8=0) (above : lower≤dst.toNat) (fits : dst.toNat+length<2^64) (before : query.toNat<lower) :
    resultMemory memory be src dst length query=memory query :=
  resultMemory_away memory be src dst query length (Away.after_floor dst query length lower aligned above fits before)

end InitECandidate.Solver.WitnessRadix.CopyGeneral

#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.Away.after_floor
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.result_before_floor
