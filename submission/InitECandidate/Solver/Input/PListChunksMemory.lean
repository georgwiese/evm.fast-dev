import InitECandidate.Solver.Input.ProgressiveMemory
import InitECandidate.Solver.Input.MixLengthMemory
import InitECandidate.Solver.Input.PListChunksCallCost
import InitECandidate.Solver.Input.IgnoredCallLookup

namespace InitECandidate.Solver.Input.PListChunks
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The original progressive list-chunk body preserves a protected decoded
word through its real tree and subsequent length mix. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (roots cursor out len stp accel chunk zeros query : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (protection : SszHash.Protected source stp accel chunk zeros query)
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (lengthLocal : source.locals.lookup (ofString "len")=some (.val (.word len)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena roots (32*n)) (temporaryArena : AllocatedBytes.Arena cursor (832+64*n))
    (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<cursor.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [body_shape] at run
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "merkleize_progressive") progressiveArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ afterRoot value (safe.summary_full source).2.1 run
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) progressiveArguments=some (Progressive.values roots (BitVec.ofNat 64 n) out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,progressiveArguments,localVar,root,count,output,Progressive.values]
  have front := Progressive.call_memory source middle roots cursor out zeros stp accel chunk query n bounded protection heap inputArena temporaryArena aligned outArena below outAway progressiveArguments args normal
  have next := SszHash.Protected.after source middle stp accel chunk zeros query protection _ none normal
    (fun key different=>progressive_globals key source.code protection.workspace.sha.installed different)
  have other (name : String) : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    CallNormal.ignored_lookup source middle (ofString name) (ofString "merkleize_progressive") progressiveArguments normal
  unfold afterRoot at remaining
  have mixSafe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "mix_in_length") mixArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨final,mixed,returned⟩ := Input.sequence_returned middle post _ _ value (mixSafe.summary_full middle).2.1 remaining
  have mixArgs : evalListHOLFinite middle (h:=fun address=>Classical.propDecidable (middle.memaddrs address)) mixArguments=some (MixLength.values out len out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,mixArguments,localVar,(other "out").trans output,(other "len").trans lengthLocal,MixLength.values]
  have mixMemory := MixLength.call_memory middle final out len out chunk zeros stp accel query next outArena outAway mixArguments mixArgs mixed
  have tail := MemoryAt.return_current final (.const 0#64) query
  rw [returned] at tail
  exact tail.trans (mixMemory.trans front)

theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (roots cursor out len stp accel chunk zeros query : BitVec 64) (n : Nat)
    (bounded : n≤134217728) (protection : SszHash.Protected source stp accel chunk zeros query)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena roots (32*n)) (temporaryArena : AllocatedBytes.Arena cursor (832+64*n))
    (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<cursor.toNat) (outAway : CopyGeneral.Away out query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values roots n len out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_plist_chunks") arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨callee,called,rootsLocal,nLocal,lenLocal,outLocal⟩ := environment source.code.lookup roots n len out (original_code source.code protection.workspace.sha.installed)
  exact MemoryAt.call_normal source post (ofString "htr_plist_chunks") arguments (values roots n len out) body callee .one query args called
    (fun target value evaluated=>body_memory (callEntryStateHOLFinite source callee) target roots cursor out len stp accel chunk zeros query n bounded
      (SszHash.Protected.at_callee source callee stp accel chunk zeros query protection) rootsLocal nLocal outLocal lenLocal heap inputArena temporaryArena aligned outArena below outAway value evaluated) run

end InitECandidate.Solver.Input.PListChunks

#print axioms InitECandidate.Solver.Input.PListChunks.body_memory
#print axioms InitECandidate.Solver.Input.PListChunks.call_memory
