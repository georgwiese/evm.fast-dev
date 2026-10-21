import InitECandidate.Solver.WitnessRadix.CopyAwayIntervals

namespace InitECandidate.Solver.WitnessRadix.CopyGeneral
open Flapjack

/-- Real literal/backing-word footprints restrict to any actual subrange,
with the original wrapping source-word address arithmetic preserved. -/
theorem Away.subrange (pointer query : BitVec 64) (total offset length : Nat)
    (away : Away pointer query total) (inside : offset+length≤total) :
    Away (pointer+BitVec.ofNat 64 offset) query length := by
  intro index bound
  have original := away (offset+index) (by omega)
  simpa only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc] using original

end InitECandidate.Solver.WitnessRadix.CopyGeneral

#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.Away.subrange
