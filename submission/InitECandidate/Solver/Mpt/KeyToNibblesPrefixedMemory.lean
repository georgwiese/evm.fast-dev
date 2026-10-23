import InitECandidate.Solver.Mpt.KeyToNibblesMemory

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack PanSemStateFiniteExact WitnessRadix WitnessRadix.QueryBranch

theorem prefix_pair_addresses (out : BitVec 64) (leading index offset : Nat) :
    firstAddress (out+BitVec.ofNat 64 leading) (BitVec.ofNat 64 index) offset=byteAddress out (leading+2*(index+offset)) ∧
    secondAddress (out+BitVec.ofNat 64 leading) (BitVec.ofNat 64 index) offset=byteAddress out (leading+2*(index+offset)+1) := by
  obtain ⟨first,second⟩:=pair_addresses (out+BitVec.ofNat 64 leading) index offset
  constructor
  · rw [first]
    simp [byteAddress,BitVec.ofNat_add,BitVec.add_assoc]
  · rw [second]
    simp [byteAddress,BitVec.ofNat_add,BitVec.add_assoc]

theorem span_address_different (out : BitVec 64) (extent left right : Nat)
    (fits : out.toNat+extent<2^64) (leftInside : left<extent) (rightInside : right<extent) (different : left≠right) :
    byteAddress out left≠byteAddress out right := by
  intro same
  have equal:=congrArg BitVec.toNat same
  rw [byteAddress_toNat out left (by omega),byteAddress_toNat out right (by omega)] at equal
  omega

/-- Extend an arbitrary actual nibble prefix with the next pair of byte
stores. This covers long witness paths and preserves an optional compact
path's first nibble, even when later stores share its backing word. -/
theorem NibblePrefix.pair_prefixed {F : Type} (source : PanSemStateFiniteExact 64 F) (out : BitVec 64)
    (leading index offset : Nat) (byte : BitVec 8) (little : source.be=false)
    (fits : out.toNat+(leading+2*(index+offset)+2)<2^64)
    (prior : NibblePrefix source out (leading+2*(index+offset)))
    (firstMapped : source.memaddrs (panByteAlignHOL (width:=64) (firstAddress (out+BitVec.ofNat 64 leading) (BitVec.ofNat 64 index) offset)))
    (secondMapped : source.memaddrs (panByteAlignHOL (width:=64) (secondAddress (out+BitVec.ofNat 64 leading) (BitVec.ofNat 64 index) offset))) :
    NibblePrefix (pairState source (out+BitVec.ofNat 64 leading) (BitVec.ofNat 64 index) offset byte) out (leading+2*(index+offset)+2) := by
  intro position inside
  have addresses:=prefix_pair_addresses out leading index offset
  have reads:=pair_reads source (out+BitVec.ofNat 64 leading) (BitVec.ofNat 64 index) offset byte little firstMapped secondMapped
  rw [addresses.1,addresses.2] at reads
  by_cases earlier : position<leading+2*(index+offset)
  · obtain ⟨value,small,read⟩:=prior position earlier
    have firstOther : firstAddress (out+BitVec.ofNat 64 leading) (BitVec.ofNat 64 index) offset≠byteAddress out position:=by
      rw [addresses.1]
      exact span_address_different out _ _ _ fits (by omega) (by omega) (by omega)
    have secondOther : secondAddress (out+BitVec.ofNat 64 leading) (BitVec.ofNat 64 index) offset≠byteAddress out position:=by
      rw [addresses.2]
      exact span_address_different out _ _ _ fits (by omega) (by omega) (by omega)
    have retained:=pair_other_byte source (out+BitVec.ofNat 64 leading) (BitVec.ofNat 64 index) (byteAddress out position) offset byte little firstOther secondOther
    refine ⟨value,small,?_⟩
    change @panMemLoadByteHOL 64 _ (pairState source (out+BitVec.ofNat 64 leading) (BitVec.ofNat 64 index) offset byte).memory source.memaddrs
      (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (byteAddress out position)=_
    rw [little,retained]
    rwa [little] at read
  · have final : position=leading+2*(index+offset) ∨ position=leading+2*(index+offset)+1:=by omega
    rcases final with rfl|rfl
    · refine ⟨UInt8.ofNat (high byte).toNat,?_,?_⟩
      · rw [UInt8.toNat_ofNat',Nat.mod_eq_of_lt (by have small:=high_small byte; omega)]
        exact high_small byte
      · change @panMemLoadByteHOL 64 _ (pairState source (out+BitVec.ofNat 64 leading) (BitVec.ofNat 64 index) offset byte).memory source.memaddrs
          (fun address=>Classical.propDecidable (source.memaddrs address)) source.be _=_
        rw [little]
        exact reads.1
    · refine ⟨UInt8.ofNat (low byte).toNat,?_,?_⟩
      · rw [UInt8.toNat_ofNat',Nat.mod_eq_of_lt (by have small:=low_small byte; omega)]
        exact low_small byte
      · change @panMemLoadByteHOL 64 _ (pairState source (out+BitVec.ofNat 64 leading) (BitVec.ofNat 64 index) offset byte).memory source.memaddrs
          (fun address=>Classical.propDecidable (source.memaddrs address)) source.be _=_
        rw [little]
        exact reads.2

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.prefix_pair_addresses
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.span_address_different
#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.NibblePrefix.pair_prefixed
