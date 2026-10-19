import InitECandidate.Solver.Mpt.TrieLookupProgram
import InitECandidate.Solver.Mpt.TrieWalkCallValues
import InitECandidate.Solver.Mpt.TrieWalkValueAgreement
import InitECandidate.Solver.Mpt.KeyToNibblesReadonlyFrame

namespace InitECandidate.Solver.Mpt.TrieLookup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

set_option maxRecDepth 100000 in
/-- Actual normal unchanged trie_lookup: the real key conversion preserves
the current structural and value words before the genuine trie tail call.
Its result is a binary triple with an actual bounded mapped payload on hits. -/
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root key out : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (valueLimit : Nat) (nodeValues : TrieWalk.Values graph valueLimit)
    (member : graph.valid root) (protectedGraph : graph.Protected out) (protectedValues : TrieWalk.ValueProtected graph out)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word root)))
    (keyCell : source.locals.lookup (ofString "key_hash32")=some (.val (.word key)))
    (scratch : source.globals.lookup (ofString "mpt_nib_scratch")=some (.val (.word out)))
    (little : source.be=false) (fits : out.toNat+64<2^64)
    (inputMapped : ∀ offset<32,source.memaddrs (panByteAlignHOL (width := 64) (byteAddress key offset)))
    (outputMapped : ∀ offset<64,source.memaddrs (panByteAlignHOL (width := 64) (byteAddress out offset)))
    (separate : ∀ left<32,∀ right<64,byteAddress key left≠byteAddress out right)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    10≤source.clock ∧ TrieWalk.Answer post.memaddrs valueLimit returned ∧ post.clock≤source.clock-10 ∧
      source.clock-2090≤post.clock ∧ KeyToNibbles.OutputFrame source post out := by
  have safe : Input.LocalPrefix (ofString "root") prepare := .call none _ _ (by intro name impossible; cases impossible)
  rw [body_shape] at normal
  obtain ⟨reached,firstRun,tailRun,rootEq⟩ := safe.normal_continue source post forward returned normal
  have firstArgs := prepare_arguments source key out keyCell scratch
  obtain ⟨funded,paid,locals,view,frame⟩ := KeyToNibbles.call_normal source reached key out little fits inputMapped outputMapped separate
    prepareArguments firstArgs installed firstRun
  obtain ⟨nextGraph,validEq,⟨nextValues⟩⟩ := TrieWalk.Values.after_output source reached graph valueLimit nodeValues out protectedGraph protectedValues frame
  have currentMember : nextGraph.valid root := by rw [validEq]; exact member
  have globalsEq := congrArg PanSemStateFiniteExact.globals frame.fields
  have codeEq := congrArg PanSemStateFiniteExact.code frame.fields
  change reached.globals=source.globals at globalsEq
  change reached.code=source.code at codeEq
  have currentRoot : reached.locals.lookup (ofString "root")=some (.val (.word root)) := by rw [locals]; exact rootCell
  have currentScratch : reached.globals.lookup (ofString "mpt_nib_scratch")=some (.val (.word out)) := by rw [globalsEq]; exact scratch
  have currentInstalled : Input.OriginalCode.Installed reached.code := by rw [codeEq]; exact installed
  have forwardArgs := forward_arguments reached root out currentRoot currentScratch
  obtain ⟨positive,answer,upper,lower,readonlyFrame⟩ := TrieWalk.Graph.tail_normal reached post nextGraph valueLimit nextValues root out 64 view currentMember
    forwardArguments forwardArgs currentInstalled returned tailRun
  have tailFrame := KeyToNibbles.OutputFrame.of_readonly reached post out readonlyFrame
  exact ⟨by omega,answer,by omega,by omega,KeyToNibbles.OutputFrame.trans source reached post out frame tailFrame⟩

end InitECandidate.Solver.Mpt.TrieLookup

#print axioms InitECandidate.Solver.Mpt.TrieLookup.body_normal
