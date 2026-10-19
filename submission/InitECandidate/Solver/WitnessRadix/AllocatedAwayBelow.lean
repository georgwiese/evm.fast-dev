import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.WitnessRadix.AllocatedBytes
open Flapjack

theorem Arena.away_below (pointer query : BitVec 64) (length : Nat) (arena : Arena pointer length)
    (aligned : pointer.toNat % 8 = 0) (below : query.toNat < pointer.toNat) :
    CopyGeneral.Away pointer query length := by
  intro offset inside
  have number := byteAddress_toNat pointer offset (by have bound := arena.upper; omega)
  have backing := aligned_number (byteAddress pointer offset)
  have division := Nat.mod_add_div pointer.toNat 8
  have byteDivision := Nat.mod_add_div (byteAddress pointer offset).toNat 8
  constructor
  · intro equal
    have equalNumber := congrArg BitVec.toNat equal
    omega
  · intro equal
    have equalNumber := congrArg BitVec.toNat equal
    omega

end InitECandidate.Solver.WitnessRadix.AllocatedBytes

#print axioms InitECandidate.Solver.WitnessRadix.AllocatedBytes.Arena.away_below
