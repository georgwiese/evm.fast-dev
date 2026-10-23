import InitECandidate.Solver.Mpt.TrieProtectedGrowth

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- A genuinely fresh path above an aligned allocation frontier avoids
every older caller word. This also covers unaligned path slices and
caller addresses; only the real allocation frontier must be aligned. -/
theorem PathWordAway.above_frontier (pointer query : BitVec 64) (length frontier : Nat)
    (fits : pointer.toNat+length<2^64) (aligned : frontier%8=0)
    (before : query.toNat<frontier) (above : frontier≤pointer.toNat) : PathWordAway pointer length query := by
  intro index inside equal
  have number:=byteAddress_toNat pointer index (by omega)
  have same:=congrArg BitVec.toNat equal
  rw [AllocatedBytes.aligned_number,number] at same
  omega

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.PathWordAway.above_frontier
