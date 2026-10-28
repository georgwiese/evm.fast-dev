import InitECandidate.Solver.Input.CurrentTable.FirstDiff.ByteReads
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Input.CurrentTable.FirstDiff
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The key actually present in the current32-byte buffer. No property of
the digest algorithm or future successful hash call is needed to name it. -/
def memoryKey (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) : KeyBits.Key :=
  fun index => match source.memory (panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 index.val)) with
    | .word word => (panGetByteHOL (pointer+BitVec.ofNat 64 index.val) word source.be).toBitVec

/-- Every actual mapped32-byte buffer has this physical key, irrespective
of its contents, alignment or byte order. -/
theorem memoryKey_view (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena pointer 32) :
    ByteView source pointer (memoryKey source pointer) := by
  intro index
  have mapped := AllocatedBytes.byte_mapped source pointer 32 index.val domain arena index.isLt
  change source.memaddrs (panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 index.val)) at mapped
  cases stored : source.memory (panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 index.val)) with
  | word word => simp [panMemLoadByteHOL,memoryKey,stored,mapped]

end InitECandidate.Solver.Input.CurrentTable.FirstDiff

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.memoryKey_view
