import InitECandidate.Solver.Mpt.TrieLookupProgram

namespace InitECandidate.Solver.Mpt.TrieLookup
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Complete unchanged trie_lookup: derive the actual converted key and
preserved graph before the real tail call. No reached key/graph or later
successful helper outcome is supplied. Startup/constructor reachability
of the current graph and scratch protection remain separate. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root key out : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (member : graph.valid root)
    (protectedGraph : graph.Protected out)
    (rootCell : source.locals.lookup (ofString "root") = some (.val (.word root)))
    (keyCell : source.locals.lookup (ofString "key_hash32") = some (.val (.word key)))
    (scratch : source.globals.lookup (ofString "mpt_nib_scratch") = some (.val (.word out)))
    (little : source.be = false) (fits : out.toNat + 64 < 2^64)
    (inputMapped : ∀ offset < 32, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress key offset)))
    (outputMapped : ∀ offset < 64, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress out offset)))
    (separate : ∀ left < 32, ∀ right < 64, byteAddress key left ≠ byteAddress out right)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock - (evaluateHOLFiniteState source body).2.clock ≤ 2090 := by
  have args := prepare_arguments source key out keyCell scratch
  have firstCost := KeyToNibbles.call_cost source key out little fits inputMapped outputMapped separate
    (some none) prepareArguments args installed
  change source.clock - (evaluateHOLFiniteState source prepare).2.clock ≤ 9 at firstCost
  have firstClock := evaluateHOLFiniteState_clock_le source prepare
  rw [body_shape, evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source prepare = output at firstCost firstClock ⊢
  obtain ⟨result, reached⟩ := output
  change source.clock - reached.clock ≤ 9 at firstCost
  change reached.clock ≤ source.clock at firstClock
  cases result with
  | none =>
    obtain ⟨funded, paid, locals, view, frame⟩ := KeyToNibbles.call_normal source reached key out little fits inputMapped outputMapped separate
      prepareArguments args installed computed
    obtain ⟨nextGraph, validEq⟩ := TrieWalk.Graph.after_output source reached graph out protectedGraph frame
    have nextMember : nextGraph.valid root := by rw [validEq]; exact member
    have globalsEq := congrArg PanSemStateFiniteExact.globals frame.fields
    have codeEq := congrArg PanSemStateFiniteExact.code frame.fields
    change reached.globals = source.globals at globalsEq
    change reached.code = source.code at codeEq
    have currentRoot : reached.locals.lookup (ofString "root") = some (.val (.word root)) := by rw [locals]; exact rootCell
    have currentScratch : reached.globals.lookup (ofString "mpt_nib_scratch") = some (.val (.word out)) := by rw [globalsEq]; exact scratch
    have currentInstalled : Input.OriginalCode.Installed reached.code := by rw [codeEq]; exact installed
    have forwardArgs := forward_arguments reached root out currentRoot currentScratch
    have secondCost := TrieWalk.Graph.call_cost reached nextGraph root out 64 view nextMember none forwardArguments forwardArgs currentInstalled
    change reached.clock - (evaluateHOLFiniteState reached forward).2.clock ≤ 2081 at secondCost
    have secondClock := evaluateHOLFiniteState_clock_le reached forward
    change source.clock - (evaluateHOLFiniteState reached forward).2.clock ≤ 2090
    omega
  | some result =>
    change source.clock - reached.clock ≤ 2090
    omega

end InitECandidate.Solver.Mpt.TrieLookup

#print axioms InitECandidate.Solver.Mpt.TrieLookup.body_cost
