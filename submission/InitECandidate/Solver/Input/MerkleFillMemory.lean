import InitECandidate.Solver.Input.MerkleBufferFill
import InitECandidate.Solver.Input.CopyAwaySubrange

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix

/-- The exact original copy/zero/declaration poststate only changes its
real buffer. fill_prefix connects this state to the actual execution. -/
theorem fill_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor query : BitVec 64) (n size : Nat)
    (inside : n≤size) (away : CopyGeneral.Away cursor query (32*size)) :
    (denseEntry source p cursor n size).memory query=source.memory query := by
  have copiedAway : CopyGeneral.Away cursor query (32*n) := by
    simpa only [BitVec.add_zero] using CopyGeneral.Away.subrange cursor query (32*size) 0 (32*n) away (by omega)
  have zeroAway := CopyGeneral.Away.subrange cursor query (32*size) (32*n) (32*(size-n)) away (by omega)
  have first := CopyGeneral.call_memory_away source p cursor query (32*n) copiedAway
  have last := Zero.final_memory_away (copiedBuffer source p cursor n).memory (cursor+BitVec.ofNat 64 (32*n)) query (32*(size-n))
    (by intro offset bound; exact (zeroAway offset bound).1)
  exact last.trans first

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.fill_memory
