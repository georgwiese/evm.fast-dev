import InitECandidate.Solver.WitnessRadix.AllocatedBytes
import InitECandidate.Solver.WitnessRadix.CopyGeneralMemory

namespace InitECandidate.Solver.WitnessRadix.CopyGeneral
open Flapjack PanSemStateFiniteExact

/-- A buffer ending before a current word cannot change that word through
either a word store or an aligned byte-store backing word. -/
theorem Away.before (pointer query : BitVec 64) (length cut : Nat)
    (before : pointer.toNat+length≤cut) (small : cut<2^64) (afterCut : cut≤query.toNat) : Away pointer query length := by
  intro offset inside
  have number := byteAddress_toNat pointer offset (by omega)
  have aligned := AllocatedBytes.aligned_number (byteAddress pointer offset)
  constructor
  · intro same
    have := congrArg BitVec.toNat same
    omega
  · intro same
    have := congrArg BitVec.toNat same
    omega

/-- A word below an aligned buffer is outside both its literal addresses
and all backing words; no mapping or future write is assumed. -/
theorem Away.after (pointer query : BitVec 64) (length : Nat)
    (aligned : pointer.toNat%8=0) (fits : pointer.toNat+length<2^64) (below : query.toNat<pointer.toNat) : Away pointer query length := by
  intro offset inside
  have number := byteAddress_toNat pointer offset (by omega)
  have backing := AllocatedBytes.aligned_number (byteAddress pointer offset)
  constructor
  · intro same
    have := congrArg BitVec.toNat same
    omega
  · intro same
    have := congrArg BitVec.toNat same
    omega

end InitECandidate.Solver.WitnessRadix.CopyGeneral

#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.Away.before
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.Away.after
