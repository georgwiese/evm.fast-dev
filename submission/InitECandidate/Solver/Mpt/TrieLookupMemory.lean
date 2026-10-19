import InitECandidate.Solver.Mpt.TrieLookupProgram
import InitECandidate.Solver.Mpt.TrieLookupCall
import InitECandidate.Solver.Mpt.KeyToNibblesReadonlyFrame
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Mpt.TrieLookup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Actual normal trie lookup writes only its nibble buffer. This memory
contract needs current conversion geometry, not a future trie/value model. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (key out : BitVec 64)
    (keyCell : source.locals.lookup (ofString "key_hash32")=some (.val (.word key)))
    (scratch : source.globals.lookup (ofString "mpt_nib_scratch")=some (.val (.word out)))
    (little : source.be=false) (fits : out.toNat+64<2^64)
    (inputMapped : ∀ offset<32,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress key offset)))
    (outputMapped : ∀ offset<64,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress out offset)))
    (separate : ∀ left<32,∀ right<64,byteAddress key left≠byteAddress out right)
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) : KeyToNibbles.OutputFrame source post out := by
  have safe : Input.LocalPrefix (ofString "root") prepare := .call none _ _ (by intro name impossible; cases impossible)
  rw [body_shape] at normal
  obtain ⟨reached,firstRun,tailRun,rootEq⟩ := safe.normal_continue source post forward returned normal
  have firstArgs := prepare_arguments source key out keyCell scratch
  obtain ⟨funded,paid,locals,view,frame⟩ := KeyToNibbles.call_normal source reached key out little fits inputMapped outputMapped separate
    prepareArguments firstArgs installed firstRun
  have codeEq := congrArg PanSemStateFiniteExact.code frame.fields
  change reached.code=source.code at codeEq
  have pure := Input.LocalEffects.call_body source.code none (ofString "trie_walk") forwardArguments TrieWalk.formals TrieWalk.body TrieWalk.resultShape
    (TrieWalk.original_code source.code installed) (TrieWalk.readonly source.code installed) reached codeEq
  change Input.LocalEffects.erase (evaluateHOLFiniteState reached forward).2=Input.LocalEffects.erase reached at pure
  rw [tailRun] at pure
  exact KeyToNibbles.OutputFrame.trans source reached post out frame (KeyToNibbles.OutputFrame.of_readonly reached post out pure)

/-- A real scoped trie caller exposes its actual callee buffer frame and
genuine continuation, without any future memory or successful run premise. -/
theorem scoped_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root key out : BitVec 64)
    (scratch : source.globals.lookup (ofString "mpt_nib_scratch")=some (.val (.word out)))
    (little : source.be=false) (fits : out.toNat+64<2^64)
    (inputMapped : ∀ offset<32,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress key offset)))
    (outputMapped : ∀ offset<64,source.memaddrs (panByteAlignHOL (width:=64) (byteAddress out offset)))
    (separate : ∀ left<32,∀ right<64,byteAddress key left≠byteAddress out right)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values root key))
    (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) TrieWalk.resultShape (ofString "trie_lookup") arguments continuation)=(some (.returned returned),post)) :
    ∃ target answer inner,KeyToNibbles.OutputFrame source target out ∧
      evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target name answer) continuation=(some (.returned returned),inner) ∧
      post=WitnessRadix.QueryBranch.restore source name inner := by
  obtain ⟨callee,called,rootLocal,keyLocal⟩ := environment source.code.lookup root key (original_code source.code installed)
  obtain ⟨positive,target,answer,inner,bodyRun,checked,tailRun,restored⟩ := Input.CallNormal.scoped_normal source post name TrieWalk.resultShape
    (ofString "trie_lookup") arguments _ body continuation callee TrieWalk.resultShape args called returned normal
  have frame := body_memory (callEntryStateHOLFinite source callee) target key out keyLocal scratch little fits inputMapped outputMapped separate installed answer bodyRun
  exact ⟨target,answer,inner,⟨frame.fields,frame.memory⟩,tailRun,restored⟩

end InitECandidate.Solver.Mpt.TrieLookup

#print axioms InitECandidate.Solver.Mpt.TrieLookup.body_memory
#print axioms InitECandidate.Solver.Mpt.TrieLookup.scoped_memory
