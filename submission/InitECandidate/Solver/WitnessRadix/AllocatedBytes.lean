import InitECandidate.Solver.WitnessRadix.AllocatedArena
import InitECandidate.Solver.WitnessRadix.CopyContext

namespace InitECandidate.Solver.WitnessRadix.AllocatedBytes
open Flapjack PanSemStateFiniteExact

theorem copy_mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (src dst : BitVec 64) (length : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (srcArena : Arena src length) (dstArena : Arena dst length) :
    CopyContext.Mapped source src dst length := by
  constructor
  · intro offset inside; exact byte_mapped source src length offset domain srcArena inside
  · intro offset inside; exact byte_mapped source dst length offset domain dstArena inside
  · intro mask offset inside aligned
    rw [BitVec.and_or_distrib_right] at mask
    have masks := BitVec.or_eq_zero_iff.mp mask
    exact word_mapped source src length offset domain srcArena inside (mask_aligned src masks.2) aligned
  · intro mask offset inside aligned
    rw [BitVec.and_or_distrib_right] at mask
    have masks := BitVec.or_eq_zero_iff.mp mask
    exact word_mapped source dst length offset domain dstArena inside (mask_aligned dst masks.1) aligned

end InitECandidate.Solver.WitnessRadix.AllocatedBytes

#print axioms InitECandidate.Solver.WitnessRadix.AllocatedBytes.copy_mapped
