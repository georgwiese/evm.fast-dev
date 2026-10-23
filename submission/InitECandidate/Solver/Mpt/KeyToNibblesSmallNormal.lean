import InitECandidate.Solver.Mpt.KeyToNibblesPrefixedNormal
import InitECandidate.Solver.Mpt.KeyToNibblesSpanAllocated

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A genuine variable-length normal conversion produces the actual nibble
view and precise write frame, without a supplied entry-clock allowance. -/
theorem small_body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64)
    (length : Nat) (small : length≤32)
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (little : source.be=false) (fits : out.toNat+64<2^64)
    (inputMapped : ∀ offset<length,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress key offset)))
    (outputMapped : ∀ offset<2*length,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress out offset)))
    (separate : ∀ left<length,∀ right<2*length,byteAddress key left≠byteAddress out right)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),target)) :
    returned=.val (.word 0#64) ∧ TrieWalk.KeyView target.memory target.memaddrs target.be out (2*length) ∧
      source.clock-target.clock≤length/4+3 ∧ SpanFrame source target out (2*length) := by
  obtain ⟨answer,nibbles⟩:=prefixed_normal source target key out 0 length (by omega) keyCell
    (by simpa only [BitVec.add_zero] using outCell) lengthCell little (by omega)
    (by simpa only [Nat.zero_add] using outputMapped) inputMapped (by intro offset impossible; omega) returned normal
  have actualCost:=body_any_cost source length (by omega) lengthCell
  rw [normal] at actualCost
  have actualFrame:=(body_span_frame source target out length (by omega) outCell lengthCell returned normal).2
  have domainEq:=congrArg PanSemStateFiniteExact.memaddrs actualFrame.fields
  change target.memaddrs=source.memaddrs at domainEq
  have view : TrieWalk.KeyView target.memory target.memaddrs target.be out (2*length):=by
    refine ⟨by omega,by omega,by rw [domainEq]; exact outputMapped,?_⟩
    change NibblePrefix target out (2*length)
    simpa only [Nat.zero_add] using nibbles
  exact ⟨answer,view,actualCost,actualFrame⟩

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.small_body_normal
