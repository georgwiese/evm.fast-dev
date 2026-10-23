import InitECandidate.Solver.Mpt.TriePathBuffer

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- An aligned lower boundary protects borrowed paths even when their
actual first byte is unaligned. This is the frame needed above scratch. -/
theorem NibbleSpan.of_aligned_band (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer : BitVec 64) (length lower upper : Nat)
    (view : NibbleSpan source.memory source.memaddrs source.be pointer length)
    (aligned : lower%8=0) (above : lower≤pointer.toNat) (before : pointer.toNat+length≤upper)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ query : BitVec 64,lower≤query.toNat→query.toNat<upper→target.memory query=source.memory query) :
    NibbleSpan target.memory target.memaddrs target.be pointer length := by
  apply view.of_agreement source.memory target.memory source.memaddrs target.memaddrs source.be target.be pointer length domain endian
  intro offset inside
  have number:=byteAddress_toNat pointer offset (by have fits:=view.fits; omega)
  apply memory
  · rw [AllocatedBytes.aligned_number,number]
    omega
  · rw [AllocatedBytes.aligned_number,number]
    omega

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.NibbleSpan.of_aligned_band
