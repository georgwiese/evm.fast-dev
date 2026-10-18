import InitECandidate.Solver.MutableTable.CopyMapped
import InitECandidate.Solver.MutableTable.NaturalLayout

namespace InitECandidate.Solver.MutableTable.MemoryRegion
open Flapjack PanSemStateFiniteExact WitnessRadix

structure Region where
  start : Nat
  length : Nat

structure Valid (region : Region) : Prop where
  lower : 2701131776 ≤ region.start
  upper : region.start + region.length ≤ 33806089496
  aligned : region.start % 8 = 0

def pointer (region : Region) : BitVec 64 := BitVec.ofNat 64 region.start
def address (region : Region) (offset : Nat) : BitVec 64 := BitVec.ofNat 64 (region.start + offset)

theorem pointer_number (region : Region) (valid : Valid region) : (pointer region).toNat = region.start := by
  rw [pointer, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := valid.upper; omega)]

theorem address_number (region : Region) (valid : Valid region) (offset : Nat) (inside : offset ≤ region.length) :
    (address region offset).toNat = region.start + offset := by
  rw [address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := valid.upper; omega)]

theorem byte_address (region : Region) (offset : Nat) : byteAddress (pointer region) offset = address region offset := by
  simp only [byteAddress, pointer, address, BitVec.ofNat_add]

theorem aligned_number (region : Region) (valid : Valid region) (offset : Nat) (inside : offset < region.length) :
    (panByteAlignHOL (width := 64) (byteAddress (pointer region) offset)).toNat = region.start + 8 * (offset / 8) := by
  rw [byte_address, ByteStore.aligned_number, address_number region valid offset (by omega)]
  have aligned := valid.aligned
  omega

/-- Every byte in an owned aligned ordinary interval has its real backing
word mapped, including a partial final word. -/
theorem byte_mapped (region : Region) (valid : Valid region) (offset : Nat) (inside : offset < region.length) :
    InitE.ordinaryDomain (panByteAlignHOL (width := 64) (byteAddress (pointer region) offset)) := by
  apply BackingLayout.ordinary_mapped
  · rw [aligned_number region valid offset inside]; have := valid.lower; omega
  · rw [aligned_number region valid offset inside]; have := valid.upper; omega
  · rw [aligned_number region valid offset inside]; have := valid.aligned; omega

/-- A memcpy destination interval cannot modify any word outside it. -/
theorem copy_away (region : Region) (valid : Valid region) (length : Nat) (fits : length ≤ region.length) (query : BitVec 64)
    (outside : query.toNat < region.start ∨ region.start + region.length ≤ query.toNat) : CopyGeneral.Away (pointer region) query length := by
  intro offset inside
  constructor
  · intro same
    have numeric := congrArg BitVec.toNat same
    rw [byte_address, address_number region valid offset (by omega)] at numeric
    omega
  · intro same
    have numeric := congrArg BitVec.toNat same
    rw [aligned_number region valid offset (by omega)] at numeric
    omega

theorem copy_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (domain : source.memaddrs = InitE.ordinaryDomain)
    (src dst : Region) (srcValid : Valid src) (dstValid : Valid dst) (length : Nat)
    (srcRoom : length ≤ src.length) (dstRoom : length ≤ dst.length) : CopyContext.Mapped source (pointer src) (pointer dst) length := by
  apply CopyMapped.of_regions
  · rw [pointer_number src srcValid]; have := srcValid.upper; omega
  · rw [pointer_number dst dstValid]; have := dstValid.upper; omega
  · intro offset inside
    rw [domain]
    exact byte_mapped src srcValid offset (by omega)
  · intro offset inside
    rw [domain]
    exact byte_mapped dst dstValid offset (by omega)

theorem pool_valid (kind : KeyHash.Kind) (plan : NaturalLayout.Plan) (valid : NaturalLayout.Valid kind plan) (pool : NaturalLayout.Pool) :
    Valid ⟨plan.base pool, NaturalLayout.size kind plan pool⟩ := ⟨valid.lower pool, valid.upper pool, valid.aligned pool⟩

theorem slice_valid (region : Region) (valid : Valid region) (offset length : Nat)
    (fits : offset + length ≤ region.length) (aligned : offset % 8 = 0) : Valid ⟨region.start + offset, length⟩ := by
  constructor
  · change 2701131776 ≤ region.start + offset
    have := valid.lower; omega
  · change region.start + offset + length ≤ 33806089496
    have := valid.upper; omega
  · change (region.start + offset) % 8 = 0
    have := valid.aligned; simp only [Nat.add_mod, this, aligned, Nat.zero_add, Nat.zero_mod]

end InitECandidate.Solver.MutableTable.MemoryRegion

#print axioms InitECandidate.Solver.MutableTable.MemoryRegion.pointer_number
#print axioms InitECandidate.Solver.MutableTable.MemoryRegion.address_number
#print axioms InitECandidate.Solver.MutableTable.MemoryRegion.byte_address
#print axioms InitECandidate.Solver.MutableTable.MemoryRegion.aligned_number
#print axioms InitECandidate.Solver.MutableTable.MemoryRegion.byte_mapped
#print axioms InitECandidate.Solver.MutableTable.MemoryRegion.copy_away
#print axioms InitECandidate.Solver.MutableTable.MemoryRegion.copy_mapped
#print axioms InitECandidate.Solver.MutableTable.MemoryRegion.pool_valid
#print axioms InitECandidate.Solver.MutableTable.MemoryRegion.slice_valid
