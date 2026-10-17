import InitECandidate.Solver.WitnessRadix.Keccak256Allocated

namespace InitECandidate.Solver.WitnessRadix.AllocatedBytes
open Flapjack PanSemStateFiniteExact

theorem Arena.away_above (pointer query : BitVec 64) (length : Nat) (arena : Arena pointer length)
    (above : pointer.toNat+length≤query.toNat) : CopyGeneral.Away pointer query length := by
  intro offset inside
  have number := byteAddress_toNat pointer offset (by have := arena.upper; omega)
  have alignedBound : (panByteAlignHOL (width := 64) (byteAddress pointer offset)).toNat≤pointer.toNat+offset := by
    rw [aligned_number,←number]
    omega
  constructor
  · intro same
    have h := congrArg BitVec.toNat same
    rw [number] at h
    omega
  · intro same
    have h := congrArg BitVec.toNat same
    omega

theorem protected_above (stp pointer scratch out query : BitVec 64) (length : Nat) (buffers : Keccak256.Buffers stp pointer scratch out length)
    (stateBefore : stp.toNat+200≤query.toNat) (scratchBefore : scratch.toNat+136≤query.toNat) (outputBefore : out.toNat+32≤query.toNat) :
    Keccak256.Protected stp scratch out query :=
  ⟨Arena.away_above stp query 200 buffers.stateArena stateBefore,
    Arena.away_above scratch query 136 buffers.scratchArena scratchBefore,
    Arena.away_above out query 32 buffers.outputArena outputBefore⟩

end InitECandidate.Solver.WitnessRadix.AllocatedBytes

#print axioms InitECandidate.Solver.WitnessRadix.AllocatedBytes.Arena.away_above
#print axioms InitECandidate.Solver.WitnessRadix.AllocatedBytes.protected_above
