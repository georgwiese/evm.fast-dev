import InitECandidate.Solver.WitnessRadix.AllocationDomain
import InitECandidate.Solver.WitnessRadix.CopyContext

namespace InitECandidate.Solver.WitnessRadix.AllocatedBytes
open Flapjack PanSemStateFiniteExact

/-- Natural extent inside the fixed ordinary-memory arena; contents and
input validity are unrestricted. Zero-length extents are allowed. -/
structure Arena (pointer : BitVec 64) (length : Nat) : Prop where
  lower : 2701131776≤pointer.toNat
  upper : pointer.toNat+length≤33806089496

theorem aligned_number (pointer : BitVec 64) :
    (panByteAlignHOL (width := 64) pointer).toNat=8*(pointer.toNat/8) := by
  have small := pointer.isLt
  change (BitVec.ofNat 64 (pointer.toNat/8*8)).toNat=_
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  omega

theorem ordinary_byte_mapped (pointer : BitVec 64) (lower : 2701131776≤pointer.toNat) (upper : pointer.toNat<33806089496) :
    InitE.ordinaryDomain (panByteAlignHOL (width := 64) pointer) := by
  apply BackingLayout.ordinary_mapped
  · rw [aligned_number]; omega
  · rw [aligned_number]; omega
  · rw [aligned_number]; omega

theorem Arena.weaken (pointer : BitVec 64) (length shorter : Nat) (arena : Arena pointer length) (inside : shorter≤length) : Arena pointer shorter :=
  ⟨arena.lower,by have := arena.upper; omega⟩

theorem Arena.subrange (pointer : BitVec 64) (length offset size : Nat) (arena : Arena pointer length) (inside : offset+size≤length) :
    Arena (byteAddress pointer offset) size := by
  have number := byteAddress_toNat pointer offset (by have := arena.upper; omega)
  constructor
  · rw [number]; have := arena.lower; omega
  · rw [number]; have := arena.upper; omega

theorem byte_mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (length offset : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : Arena pointer length) (inside : offset<length) :
    source.memaddrs (panByteAlignHOL (width := 64) (byteAddress pointer offset)) := by
  rw [domain]
  have number := byteAddress_toNat pointer offset (by have := arena.upper; omega)
  apply ordinary_byte_mapped
  · rw [number]; have := arena.lower; omega
  · rw [number]; have := arena.upper; omega

theorem word_mapped {F : Type} (source : PanSemStateFiniteExact 64 F) (pointer : BitVec 64) (length offset : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : Arena pointer length) (inside : offset<length)
    (pointerAligned : pointer.toNat%8=0) (offsetAligned : offset%8=0) : source.memaddrs (byteAddress pointer offset) := by
  rw [domain]
  have number := byteAddress_toNat pointer offset (by have := arena.upper; omega)
  apply BackingLayout.ordinary_mapped
  · rw [number]; have := arena.lower; omega
  · rw [number]; have := arena.upper; omega
  · rw [number,Nat.add_mod,pointerAligned,offsetAligned]

theorem mask_aligned (pointer : BitVec 64) (mask : pointer &&& 7#64=0#64) : pointer.toNat%8=0 := by
  have h := congrArg BitVec.toNat mask
  rw [BitVec.toNat_and] at h
  change pointer.toNat &&& 7=0 at h
  rw [show 7=2^3-1 from rfl,Nat.and_two_pow_sub_one_eq_mod] at h
  exact h

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

#print axioms InitECandidate.Solver.WitnessRadix.AllocatedBytes.aligned_number
#print axioms InitECandidate.Solver.WitnessRadix.AllocatedBytes.ordinary_byte_mapped
#print axioms InitECandidate.Solver.WitnessRadix.AllocatedBytes.Arena.weaken
#print axioms InitECandidate.Solver.WitnessRadix.AllocatedBytes.Arena.subrange
#print axioms InitECandidate.Solver.WitnessRadix.AllocatedBytes.byte_mapped
#print axioms InitECandidate.Solver.WitnessRadix.AllocatedBytes.word_mapped
#print axioms InitECandidate.Solver.WitnessRadix.AllocatedBytes.mask_aligned
#print axioms InitECandidate.Solver.WitnessRadix.AllocatedBytes.copy_mapped
