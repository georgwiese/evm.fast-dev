import InitECandidate.Solver.Input.RlpWrite.BytesWriteCall
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Input.RlpWrite
open Flapjack PanSemStateFiniteExact

theorem byte_read_exists (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (mapped : source.memaddrs (panByteAlignHOL (width:=64) pointer)) :
    ∃ byte,@panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address=>Classical.propDecidable (source.memaddrs address)) source.be pointer=some byte := by
  classical
  cases stored : source.memory (panByteAlignHOL (width:=64) pointer) with
  | word value=>simp [panMemLoadByteHOL,mapped,stored]

/-- Derive every actual byte-encoder access from two ordinary-memory extents.
The first byte is read only for a single-byte item; empty items are included. -/
theorem bytes_access (source : PanSemStateFiniteExact 64 Guest.HostMemory) (dst src : BitVec 64) (length : Nat) (small : length≤134217712)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (srcArena : WitnessRadix.AllocatedBytes.Arena src length) (dstArena : WitnessRadix.AllocatedBytes.Arena dst (length+9)) :
    ∃ byte,BytesWrite.Access source dst src length byte := by
  classical
  have headerMapped : ∀ index<9,source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index)) := by
    intro index inside
    exact WitnessRadix.AllocatedBytes.byte_mapped source dst (length+9) index domain dstArena (by omega)
  have copyMapped : ∀ header,1≤header→header≤9→WitnessRadix.CopyContext.Mapped source src (dst+BitVec.ofNat 64 header) length := by
    intro header lower upper
    have destination:=WitnessRadix.AllocatedBytes.Arena.subrange dst (length+9) header length dstArena (by omega)
    exact WitnessRadix.AllocatedBytes.copy_mapped source src (dst+BitVec.ofNat 64 header) length domain srcArena destination
  by_cases one : length=1
  · have mapped : source.memaddrs (panByteAlignHOL (width:=64) src) := by
      simpa [WitnessRadix.byteAddress] using
        WitnessRadix.AllocatedBytes.byte_mapped source src length 0 domain srcArena (by omega)
    obtain ⟨byte,loaded⟩:=byte_read_exists source src mapped
    exact ⟨byte,⟨small,by intro; exact loaded,headerMapped,copyMapped⟩⟩
  · exact ⟨0,⟨small,by intro impossible; exact (one impossible).elim,headerMapped,copyMapped⟩⟩

end InitECandidate.Solver.Input.RlpWrite

#print axioms InitECandidate.Solver.Input.RlpWrite.byte_read_exists
#print axioms InitECandidate.Solver.Input.RlpWrite.bytes_access
