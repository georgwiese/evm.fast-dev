import InitECandidate.Solver.Mpt.TrieLookupNormal
import InitECandidate.Solver.Mpt.TrieLookupCall
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Mpt.TrieLookup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

set_option maxRecDepth 100000 in
/-- The actual scoped lookup supplies its genuine binary/payload result to
the real caller continuation. Current entry values/scratch are the premises;
funding, callee result and continuation execution are conclusions. -/
theorem scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root key out : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (valueLimit : Nat) (nodeValues : TrieWalk.Values graph valueLimit)
    (member : graph.valid root) (protectedGraph : graph.Protected out) (protectedValues : TrieWalk.ValueProtected graph out)
    (scratch : source.globals.lookup (ofString "mpt_nib_scratch")=some (.val (.word out)))
    (little : source.be=false) (fits : out.toNat+64<2^64)
    (inputMapped : ∀ offset<32,source.memaddrs (panByteAlignHOL (width := 64) (byteAddress key offset)))
    (outputMapped : ∀ offset<64,source.memaddrs (panByteAlignHOL (width := 64) (byteAddress out offset)))
    (separate : ∀ left<32,∀ right<64,byteAddress key left≠byteAddress out right)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments=some (values root key))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) TrieWalk.resultShape (ofString "trie_lookup") arguments continuation)=(some (.returned returned),post)) :
    11≤source.clock ∧ ∃ target answer inner,
      TrieWalk.Answer target.memaddrs valueLimit answer ∧ target.clock≤source.clock-11 ∧ source.clock-2091≤target.clock ∧
      KeyToNibbles.OutputFrame source target out ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name answer) continuation=(some (.returned returned),inner) ∧
      post=WitnessRadix.QueryBranch.restore source name inner := by
  obtain ⟨callee,called,rootLocal,keyLocal⟩ := environment source.code.lookup root key (original_code source.code installed)
  obtain ⟨positive,target,answer,inner,bodyRun,checked,continuationRun,restored⟩ :=
    Input.CallNormal.scoped_normal source post name TrieWalk.resultShape (ofString "trie_lookup") arguments _ body continuation callee TrieWalk.resultShape args called returned normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨funded,result,upper,lower,frame⟩ := body_normal entry target root key out graph valueLimit nodeValues member protectedGraph protectedValues rootLocal keyLocal scratch little fits inputMapped outputMapped separate installed answer bodyRun
  change 10≤source.clock-1 at funded
  change target.clock≤source.clock-1-10 at upper
  change source.clock-1-2090≤target.clock at lower
  exact ⟨by omega,target,answer,inner,result,by omega,by omega,⟨frame.fields,frame.memory⟩,continuationRun,restored⟩

end InitECandidate.Solver.Mpt.TrieLookup

#print axioms InitECandidate.Solver.Mpt.TrieLookup.scoped_normal
