import InitECandidate.Solver.Mpt.KeyToNibblesPrefixedNormal
import InitECandidate.Solver.Mpt.KeyToNibblesAnyCall
import InitECandidate.Solver.Input.IgnoredCallTarget

namespace InitECandidate.Solver.Mpt.KeyToNibbles
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The genuine ignored converter call establishes the long-path nibble
range at its actual caller state, preserving an existing compact nibble.
The ABI and normal child execution are derived from this real call. -/
theorem prefixed_call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64)
    (leading length : Nat) (small : length≤1024) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some (anyValues key (BitVec.ofNat 64 length) (out+BitVec.ofNat 64 leading)))
    (installed : Input.OriginalCode.Installed source.code) (little : source.be=false)
    (fits : out.toNat+(leading+2*length)<2^64)
    (mapped : ∀ offset<leading+2*length,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress out offset)))
    (inputMapped : ∀ offset<length,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress key offset)))
    (prior : NibblePrefix source out leading)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "key_to_nibbles") arguments)=(none,target)) :
    NibblePrefix target out (leading+2*length) ∧ source.clock-target.clock≤length/4+4 := by
  obtain ⟨callee,called,keyCell,lengthCell,outCell⟩:=any_environment source.code.lookup key (BitVec.ofNat 64 length) (out+BitVec.ofNat 64 leading)
    (original_code source.code installed)
  obtain ⟨funded,child,returned,run⟩:=Input.CallNormal.ignored_callee_return source target (ofString "key_to_nibbles") arguments _ body callee .one args called normal
  obtain ⟨answer,nibbles⟩:=prefixed_normal (callEntryStateHOLFinite source callee) child key out leading length small keyCell outCell lengthCell little
    fits mapped inputMapped prior returned run
  have endpoint:=Input.CallNormal.ignored_target source target (ofString "key_to_nibbles") arguments _ body callee .one args called returned child run normal
  have price:=call_any_cost source key (out+BitVec.ofNat 64 leading) length (by omega) (some none) arguments args installed
  change source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "key_to_nibbles") arguments)).2.clock≤length/4+4 at price
  rw [normal] at price
  refine ⟨?_,price⟩
  rw [endpoint]
  exact nibbles

end InitECandidate.Solver.Mpt.KeyToNibbles

#print axioms InitECandidate.Solver.Mpt.KeyToNibbles.prefixed_call_normal
