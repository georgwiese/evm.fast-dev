import InitECandidate.Solver.Mpt.TrieWalkMemory
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Full actual stored-path bytes, allowing long decoded paths. A future
branch split can inspect the byte after a matched short query prefix. -/
structure NibbleSpan (memory : Memory) (domain : BitVec 64 → Prop) (be : Bool) (pointer : BitVec 64) (length : Nat) : Prop where
  fits : pointer.toNat+length<2^64
  mapped : ∀ offset<length,domain (panByteAlignHOL (width:=64) (byteAddress pointer offset))
  nibble : ∀ offset<length,∃ value : UInt8,value.toNat<16 ∧
    @panMemLoadByteHOL 64 _ memory domain (fun query=>Classical.propDecidable (domain query)) be (byteAddress pointer offset)=some value

theorem KeyView.nibble_span (memory : Memory) (domain : BitVec 64 → Prop) (be : Bool) (pointer : BitVec 64) (length : Nat)
    (view : KeyView memory domain be pointer length) : NibbleSpan memory domain be pointer length:=
  ⟨view.fits,view.mapped,view.nibble⟩

theorem NibbleSpan.key_view (memory : Memory) (domain : BitVec 64 → Prop) (be : Bool) (pointer : BitVec 64) (length : Nat)
    (view : NibbleSpan memory domain be pointer length) (small : length≤64) : KeyView memory domain be pointer length:=
  ⟨small,view.fits,view.mapped,view.nibble⟩

/-- Actual prefixes and suffixes borrow the original nibble buffer while
retaining full mapping, no wrapping, and every byte's genuine range. -/
theorem NibbleSpan.window (memory : Memory) (domain : BitVec 64 → Prop) (be : Bool) (pointer position : BitVec 64) (length count : Nat)
    (view : NibbleSpan memory domain be pointer length) (bounded : position.toNat≤length) (within : count≤length-position.toNat) :
    NibbleSpan memory domain be (pointer+position) count := by
  have addition : (pointer+position).toNat=pointer.toNat+position.toNat:=BitVec.toNat_add_of_lt (by have fits:=view.fits; omega)
  have shifted (offset : Nat) : byteAddress (pointer+position) offset=byteAddress pointer (position.toNat+offset):=by
    simp [byteAddress,BitVec.ofNat_add,BitVec.add_assoc]
  refine ⟨by rw [addition]; have fits:=view.fits; omega,?_,?_⟩
  · intro offset inside
    rw [shifted]
    exact view.mapped _ (by omega)
  · intro offset inside
    rw [shifted]
    exact view.nibble _ (by omega)

theorem NibbleSpan.of_agreement (memory memory' : Memory) (domain domain' : BitVec 64 → Prop) (be be' : Bool)
    (pointer : BitVec 64) (length : Nat) (view : NibbleSpan memory domain be pointer length)
    (sameDomain : domain'=domain) (sameEndian : be'=be)
    (agree : ∀ offset<length,memory' (panByteAlignHOL (width:=64) (byteAddress pointer offset))=
      memory (panByteAlignHOL (width:=64) (byteAddress pointer offset))) : NibbleSpan memory' domain' be' pointer length := by
  subst domain'
  subst be'
  refine ⟨view.fits,view.mapped,?_⟩
  intro offset inside
  obtain ⟨value,small,read⟩:=view.nibble offset inside
  refine ⟨value,small,?_⟩
  have equal : @panMemLoadByteHOL 64 _ memory' domain (fun query=>Classical.propDecidable (domain query)) be (byteAddress pointer offset)=
      @panMemLoadByteHOL 64 _ memory domain (fun query=>Classical.propDecidable (domain query)) be (byteAddress pointer offset):=by
    simp only [panMemLoadByteHOL,agree offset inside]
  exact equal.trans read

/-- A true frame below a fresh allocation preserves every older nibble,
including an unaligned final byte's complete backing word. -/
theorem NibbleSpan.of_before (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (length cutoff : Nat)
    (view : NibbleSpan source.memory source.memaddrs source.be pointer length)
    (before : pointer.toNat+length≤cutoff) (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ query : BitVec 64,query.toNat<cutoff → target.memory query=source.memory query) :
    NibbleSpan target.memory target.memaddrs target.be pointer length := by
  apply view.of_agreement source.memory target.memory source.memaddrs target.memaddrs source.be target.be pointer length domain endian
  intro offset inside
  have number:=byteAddress_toNat pointer offset (by have fits:=view.fits; omega)
  have backing : (panByteAlignHOL (width:=64) (byteAddress pointer offset)).toNat≤(byteAddress pointer offset).toNat:=by
    rw [AllocatedBytes.aligned_number]
    omega
  apply memory
  rw [number] at backing
  omega

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.KeyView.nibble_span
#print axioms InitECandidate.Solver.Mpt.TrieWalk.NibbleSpan.key_view
#print axioms InitECandidate.Solver.Mpt.TrieWalk.NibbleSpan.window
#print axioms InitECandidate.Solver.Mpt.TrieWalk.NibbleSpan.of_agreement
#print axioms InitECandidate.Solver.Mpt.TrieWalk.NibbleSpan.of_before
