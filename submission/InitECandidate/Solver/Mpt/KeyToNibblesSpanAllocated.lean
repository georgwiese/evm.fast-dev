import InitECandidate.Solver.Mpt.KeyToNibblesSpanCall
import InitECandidate.Solver.MutableTable.MemoryRegion

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Place the actual converter output inside its genuine enclosing fresh
allocation, including an unaligned first-nibble displacement. Aligned byte
backing words cannot escape that allocation's physical interval. -/
theorem SpanFrame.allocated_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (base : BitVec 64) (allocation displacement length : Nat)
    (frame : SpanFrame source target (byteAddress base displacement) length)
    (arena : AllocatedBytes.Arena base allocation) (aligned : base.toNat%8=0) (inside : displacement+length≤allocation) :
    ∀ query : BitVec 64,query.toNat<base.toNat ∨ base.toNat+allocation≤query.toNat→target.memory query=source.memory query := by
  let region : MutableTable.MemoryRegion.Region:=⟨base.toNat,allocation⟩
  have valid : MutableTable.MemoryRegion.Valid region:=⟨arena.lower,arena.upper,aligned⟩
  have pointerEq : MutableTable.MemoryRegion.pointer region=base:=by simp [MutableTable.MemoryRegion.pointer,region]
  intro query outside
  apply frame.memory query
  intro offset bound same
  have combined : byteAddress (byteAddress base displacement) offset=byteAddress base (displacement+offset):=by
    simp only [byteAddress,BitVec.ofNat_add,BitVec.add_assoc]
  have numeric:=congrArg BitVec.toNat same
  rw [combined,←pointerEq,MutableTable.MemoryRegion.aligned_number region valid (displacement+offset) (by change displacement+offset<allocation; omega)] at numeric
  change query.toNat=base.toNat+8*((displacement+offset)/8) at numeric
  omega

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.SpanFrame.allocated_frame
