import InitECandidate.Solver.Mpt.AccountObjectGeometry
import InitECandidate.Solver.MutableTable.CopyAlignedContents

namespace InitECandidate.Solver.Mpt.AccountCopy
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable

def region (pointer : BitVec 64) : MemoryRegion.Region := ⟨pointer.toNat,56⟩
theorem region_valid (pointer : BitVec 64) (output : AccountDecode.Output pointer) : MemoryRegion.Valid (region pointer) :=
  ⟨output.lower,output.upper,output.aligned⟩
theorem region_pointer (pointer : BitVec 64) : MemoryRegion.pointer (region pointer)=pointer := by
  simp only [MemoryRegion.pointer,region,BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem aligned (src dst : BitVec 64) (source : AccountDecode.Output src) (target : AccountDecode.Output dst) : CopyGeneral.aligned src dst := by
  have actual := CopyContents.regions_aligned (region src) (region dst) (region_valid src source) (region_valid dst target)
  simpa only [region_pointer] using actual

theorem copy_price (src dst : BitVec 64) (source : AccountDecode.Output src) (target : AccountDecode.Output dst) : CopyGeneral.cost src dst 56=4 := by
  rw [CopyGeneral.cost,if_pos (aligned src dst source target)]
  rfl

/-- Original aligned memcpy reproduces all seven words, and hence both
real account references, in a fresh separated56-byte account. -/
def copied_image (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (src dst : BitVec 64)
    (image : AccountDecode.Image source src) (output : AccountDecode.Output dst) (earlier : src.toNat+56≤dst.toNat)
    (domain : target.memaddrs=source.memaddrs)
    (memory : target.memory=CopyGeneral.resultMemory source.memory source.be src dst 56) : AccountDecode.Image target dst := by
  have copied (offset : Nat) (inside : offset<56) (alignedOffset : offset%8=0) :
      CopyGeneral.resultMemory source.memory source.be src dst 56 (dst+BitVec.ofNat 64 offset)=source.memory (src+BitVec.ofNat 64 offset) := by
    have actual := CopyContents.word_at source.memory source.be (region src) (region dst) (region_valid src image.output) (region_valid dst output)
      (Or.inl earlier) 56 (Nat.le_refl _) (Nat.le_refl _) (by decide) offset inside alignedOffset
    simpa only [region_pointer,byteAddress] using actual
  refine ⟨output,domain.trans image.domain,image.root,image.hash,?_,?_,image.rootArena,image.hashArena⟩
  · rw [memory,copied 40 (by decide) (by decide)]
    exact image.rootStored
  · rw [memory,copied 48 (by decide) (by decide)]
    exact image.hashStored

theorem copy_window (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (src dst : BitVec 64)
    (output : AccountDecode.Output dst) (memory : target.memory=CopyGeneral.resultMemory source.memory source.be src dst 56) :
    Rlp.Slices.Window source target dst.toNat (dst.toNat+56) := by
  intro query outside
  have away := MemoryRegion.copy_away (region dst) (region_valid dst output) 56 (Nat.le_refl _) query outside
  simp only [region_pointer] at away
  rw [memory]
  exact CopyGeneral.resultMemory_away source.memory source.be src dst query 56 away

end InitECandidate.Solver.Mpt.AccountCopy

#print axioms InitECandidate.Solver.Mpt.AccountCopy.region_valid
#print axioms InitECandidate.Solver.Mpt.AccountCopy.region_pointer
#print axioms InitECandidate.Solver.Mpt.AccountCopy.aligned
#print axioms InitECandidate.Solver.Mpt.AccountCopy.copy_price
#print axioms InitECandidate.Solver.Mpt.AccountCopy.copied_image
#print axioms InitECandidate.Solver.Mpt.AccountCopy.copy_window
