import InitECandidate.Solver.MutableTable.CopyByteContents
import InitECandidate.Solver.WitnessRadix.Addressing

namespace InitECandidate.Solver.WitnessRadix.CopyByteContent
open Flapjack MutableTable.CopyContents

/-- Actual disjoint forward-copy byte intervals. Neither pointer needs
word alignment; original trie path slices may be unaligned. -/
structure Range (src dst : BitVec 64) (length : Nat) : Prop where
  sourceFits : src.toNat+length<2^64
  destinationFits : dst.toNat+length<2^64
  apart : src.toNat+length≤dst.toNat

theorem Range.separate (src dst : BitVec 64) (length : Nat) (range : Range src dst length)
    (first second : Nat) (firstInside : first<length) (secondInside : second<length) :
    byteAddress src first≠byteAddress dst second := by
  intro equal
  have number:=congrArg BitVec.toNat equal
  rw [byteAddress_toNat src first (by have bound:=range.sourceFits; omega),
    byteAddress_toNat dst second (by have bound:=range.destinationFits; omega)] at number
  have apart:=range.apart
  omega

theorem Range.destination_injective (src dst : BitVec 64) (length : Nat) (range : Range src dst length)
    (first second : Nat) (firstInside : first<length) (secondInside : second<length)
    (equal : byteAddress dst first=byteAddress dst second) : first=second := by
  have number:=congrArg BitVec.toNat equal
  rw [byteAddress_toNat dst first (by have bound:=range.destinationFits; omega),
    byteAddress_toNat dst second (by have bound:=range.destinationFits; omega)] at number
  omega

/-- Source bytes stay at their snapshot values, while every byte already
copied to the destination has the corresponding snapshot value. -/
structure Prefix (snapshot memory : WordWrites.Memory) (src dst : BitVec 64) (length copied : Nat) : Prop where
  source : ∀ offset<length,byte memory (byteAddress src offset)=byte snapshot (byteAddress src offset)
  destination : ∀ offset<copied,byte memory (byteAddress dst offset)=byte snapshot (byteAddress src offset)

theorem prefix_initial (memory : WordWrites.Memory) (src dst : BitVec 64) (length : Nat) : Prefix memory memory src dst length 0 :=
  ⟨by intro offset inside; rfl,by intro offset inside; omega⟩

theorem byte_step_projection (memory : WordWrites.Memory) (src dst query : BitVec 64) (index : Nat) :
    byte (CopyBytes.copyMemory memory false src dst (BitVec.ofNat 64 index) 0) query=
      if query=byteAddress dst index then byte memory (byteAddress src index) else byte memory query := by
  have projected:=byte_copy_projection memory src dst (BitVec.ofNat 64 index) query 0
  simp only [BitVec.add_zero] at projected
  unfold byteAddress
  by_cases same : query=dst+BitVec.ofNat 64 index
  · rw [if_pos same]
    rw [if_pos same] at projected
    exact projected
  · rw [if_neg same]
    rw [if_neg same] at projected
    exact projected

/-- One actual byte copy extends the correct prefix and retains all
source bytes, including other lanes of its destination backing word. -/
theorem Prefix.byte_step (snapshot memory : WordWrites.Memory) (src dst : BitVec 64) (length index : Nat)
    (range : Range src dst length) (prefixModel : Prefix snapshot memory src dst length index) (inside : index<length) :
    Prefix snapshot (CopyBytes.copyMemory memory false src dst (BitVec.ofNat 64 index) 0) src dst length (index+1) := by
  constructor
  · intro offset inSource
    rw [byte_step_projection,if_neg (range.separate src dst length offset index inSource inside)]
    exact prefixModel.source offset inSource
  · intro offset inPrefix
    rw [byte_step_projection]
    by_cases same : offset=index
    · subst offset
      rw [if_pos rfl]
      exact prefixModel.source index inside
    · have before : offset<index:=by omega
      have different : byteAddress dst offset≠byteAddress dst index:=by
        intro equal
        exact same (range.destination_injective src dst length offset index (by omega) inside equal)
      rw [if_neg different]
      exact prefixModel.destination offset before

end InitECandidate.Solver.WitnessRadix.CopyByteContent

#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.Range.separate
#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.Range.destination_injective
#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.prefix_initial
#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.byte_step_projection
#print axioms InitECandidate.Solver.WitnessRadix.CopyByteContent.Prefix.byte_step
