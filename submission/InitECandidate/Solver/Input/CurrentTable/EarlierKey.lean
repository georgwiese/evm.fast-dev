import InitECandidate.Solver.Input.CurrentTable.FirstDiff.ByteReads
import InitECandidate.Solver.Input.MemoryMetadata
import InitECandidate.Solver.WitnessRadix.AllocatedArena

namespace InitECandidate.Solver.Input.CurrentTable.FirstDiff
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Physical earlier byte keys survive a memory-write prefix. The frame
is checked at each byte's actual aligned backing cell. -/
theorem ByteView.before_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer : BitVec 64} {key : KeyBits.Key} (frontier : Nat)
    (domain : target.memaddrs = source.memaddrs) (endian : target.be = source.be)
    (memory : ∀ address : BitVec 64,address.toNat < frontier → target.memory address = source.memory address)
    (fits : pointer.toNat+32 < 2^64) (before : pointer.toNat+32 ≤ frontier) (view : ByteView source pointer key) :
    ByteView target pointer key := by
  intro byte
  have number := byteAddress_toNat pointer byte.val (by have := byte.isLt; omega)
  change (pointer+BitVec.ofNat 64 byte.val).toNat = pointer.toNat+byte.val at number
  have backing := AllocatedBytes.aligned_number (pointer+BitVec.ofNat 64 byte.val)
  rw [number] at backing
  have beforeCell : (panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 byte.val)).toNat < frontier := by
    have := byte.isLt
    omega
  have kept := memory _ beforeCell
  by_cases mapped : source.memaddrs (panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 byte.val))
  all_goals simpa [panMemLoadByteHOL,domain,endian,kept,mapped] using view byte

end InitECandidate.Solver.Input.CurrentTable.FirstDiff

#print axioms InitECandidate.Solver.Input.CurrentTable.FirstDiff.ByteView.before_frame
