import InitECandidate.Solver.Mpt.CommonPrefixCall
import InitECandidate.Solver.Input.ScopedCallNone
import InitECandidate.Solver.Input.EraseResume

namespace InitECandidate.Solver.Mpt.CommonPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuinely continuing original comparison derives its bounded
returned word and exact caller continuation. No equality of input bytes
or later successful traversal is supplied as a premise. -/
theorem none_prefix (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (a left b right : BitVec 64)
    (small : min left.toNat right.toNat≤64) (installed : Input.OriginalCode.Installed source.code)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (values a left b right))
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "common_prefix_length") arguments continuation)=(none,target)) :
    ∃ word clock inner,word.toNat≤min left.toNat right.toNat ∧ source.clock-clock≤min left.toNat right.toNat+2 ∧ clock≤source.clock ∧
      evaluateHOLFiniteState (QueryBranch.bind {source with clock:=clock} name word) continuation=(none,inner) ∧ target=restore source name inner := by
  obtain ⟨callee,called,_aCell,leftCell,_bCell,rightCell⟩:=environment source.code.lookup a left b right (original_code source.code installed)
  obtain ⟨_funded,child,returned,inner,run,_checked,continued,endpoint⟩:=Input.CallNormal.scoped_none source target name .one (ofString "common_prefix_length") arguments _ body continuation callee .one args called normal
  obtain ⟨word,answer,bound,price,frame⟩:=body_normal (callEntryStateHOLFinite source callee) child left right small installed leftCell rightCell returned run
  have canonical:=Input.CallNormal.continuation_of_erase source child name returned frame
  rw [answer] at canonical
  rw [answer,canonical] at continued
  have forward:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
  rw [run] at forward
  change child.clock≤source.clock-1 at forward
  have callerPrice : source.clock-child.clock≤min left.toNat right.toNat+2:=by
    change source.clock-1-child.clock≤min left.toNat right.toNat+1 at price
    omega
  exact ⟨word,child.clock,inner,bound,callerPrice,(by omega),continued,endpoint⟩

end InitECandidate.Solver.Mpt.CommonPrefix

#print axioms InitECandidate.Solver.Mpt.CommonPrefix.none_prefix
