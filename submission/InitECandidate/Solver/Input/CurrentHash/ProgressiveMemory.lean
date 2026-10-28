import InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryLoop
import InitECandidate.Solver.Input.CurrentHash.ProgressiveMemoryFold
import InitECandidate.Solver.Input.CurrentHash.MemoryContextAllocation
import InitECandidate.Solver.Input.CurrentHash.MarkedHeap
import InitECandidate.Solver.Input.CurrentHash.ProgressiveEnvironment

namespace InitECandidate.Solver.Input.CurrentHash.ProgressiveMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open Progressive ProgressiveRound ProgressiveBodyCost

theorem loop_suffix_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots acc cursor out zeros query : BitVec 64) (n k : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : Round source p roots n k) (bounded : n≤134217728) (round : k≤15)
    (accLocal : source.locals.lookup (ofString "acc")=some (.val (.word acc)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena p (32*n)) (rootsArena : AllocatedBytes.Arena roots 768) (accArena : AllocatedBytes.Arena acc 32)
    (outArena : AllocatedBytes.Arena out 32) (accAligned : acc.toNat%8=0)
    (rootsAway : CopyGeneral.Away roots query 768) (accAway : CopyGeneral.Away acc query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source loopAndSuffix=(some (.returned value),post)) : post.memory query=source.memory query := by
  have safe (name : String) (notCnt : ofString name≠ofString "cnt") (notOff : ofString name≠ofString "off")
      (notSize : ofString name≠ofString "size") (notK : ofString name≠ofString "k") : LocalPrefix (ofString name) loop := by
    rw [loop_shape.1]
    exact .loop _ (step_other _ notCnt notOff notSize notK)
  rw [fold_shape.2.2.1] at actual
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value ((safe "acc" (by decide) (by decide) (by decide) (by decide)).summary_full source).2.1 actual
  have image := ProgressiveMemoryLoop.frame source middle p roots cursor zeros query n k context data bounded round inputArena rootsArena rootsAway normal
  have accSummary := (safe "acc" (by decide) (by decide) (by decide) (by decide)).summary_full source
  have outSummary := (safe "out" (by decide) (by decide) (by decide) (by decide)).summary_full source
  unfold LocalSummary at accSummary outSummary
  rw [normal] at accSummary outSummary
  have next : ProgressiveMemoryFold.Params middle acc out := ⟨image.2.1.installed,image.2.1.domain,(accSummary.1 rfl).trans accLocal,(outSummary.1 rfl).trans output⟩
  exact (ProgressiveMemoryFold.suffix_memory middle post acc out query next accArena outArena accAligned accAway outAway value remaining).trans image.1

theorem initialized_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots acc cursor out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (bounded : n≤134217728)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (accLocal : source.locals.lookup (ofString "acc")=some (.val (.word acc)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena p (32*n)) (rootsArena : AllocatedBytes.Arena roots 768) (accArena : AllocatedBytes.Arena acc 32)
    (outArena : AllocatedBytes.Arena out 32) (accAligned : acc.toNat%8=0)
    (rootsAway : CopyGeneral.Away roots query 768) (accAway : CopyGeneral.Away acc query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterAcc=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [prefix_shape.2.2.2.1] at actual
  obtain ⟨firstPost,runFirst,endpointFirst⟩ := declaration_return_word source post "k" (.const 0#64) 0#64 afterK value rfl actual
  let firstState := bind source "k" 0#64
  rw [prefix_shape.2.2.2.2.1] at runFirst
  obtain ⟨secondPost,runSecond,endpointSecond⟩ := declaration_return_word firstState firstPost "off" (.const 0#64) 0#64 afterOff value rfl runFirst
  let secondState := bind firstState "off" 0#64
  rw [prefix_shape.2.2.2.2.2] at runSecond
  obtain ⟨thirdPost,runThird,endpointThird⟩ := declaration_return_word secondState secondPost "size" (.const 1#64) 1#64 loopAndSuffix value rfl runSecond
  have kept (name : String) (notK : ofString "k"≠ofString name) (notOff : ofString "off"≠ofString name) (notSize : ofString "size"≠ofString name) :
      (initialized source).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    (bind_lookup_other _ "size" name _ notSize).trans ((bind_lookup_other _ "off" name _ notOff).trans (bind_lookup_other source "k" name _ notK))
  have image := loop_suffix_memory (initialized source) thirdPost p roots acc cursor out zeros query n 0 (context.of_frozen rfl)
    (initialized_round source p roots n pointer root count) bounded (by decide) ((kept "acc" (by decide) (by decide) (by decide)).trans accLocal)
    ((kept "out" (by decide) (by decide) (by decide)).trans output) inputArena rootsArena accArena outArena accAligned rootsAway accAway outAway value runThird
  rw [endpointFirst,endpointSecond,endpointThird]
  exact image

theorem after_roots_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots acc out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source acc zeros query) (bounded : n≤134217728)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (root : source.locals.lookup (ofString "roots")=some (.val (.word roots)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena p (32*n)) (rootsArena : AllocatedBytes.Arena roots 768)
    (outArena : AllocatedBytes.Arena out 32) (rootsAway : CopyGeneral.Away roots query 768) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterRoots=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [prefix_shape.2.2.1] at actual
  apply MemoryContextAllocation.scope_memory source post acc 32#64 zeros query context "acc" [.const 32#64] afterAcc rfl _ value actual
  intro inner ready arena returned remaining
  let entry := MemoryContextAllocation.entry source acc 32#64 "acc"
  have kept (name : String) (different : ofString "acc"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    bind_lookup_other (PersistentAlloc.post {source with clock:=source.clock-1} acc 32#64) "acc" name acc different
  have away := CopyGeneral.Away.after acc query 32 context.aligned (by have h:=arena.upper; omega) context.below
  exact initialized_memory entry inner p roots acc (PersistentAlloc.rounded acc 32#64) out zeros query n ready bounded
    ((kept "p" (by decide)).trans pointer) ((kept "roots" (by decide)).trans root) ((kept "n" (by decide)).trans count)
    (bind_lookup_same _ _ _) ((kept "out" (by decide)).trans output) inputArena rootsArena arena outArena context.aligned rootsAway away outAway returned remaining

theorem after_mark_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source roots zeros query) (bounded : n≤134217728)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena p (32*n)) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [prefix_shape.2.1] at actual
  apply MemoryContextAllocation.scope_memory source post roots 768#64 zeros query context "roots" [.panop .mul [.const 24#64,.const 32#64]] afterRoots rfl _ value actual
  intro inner ready arena returned remaining
  let entry := MemoryContextAllocation.entry source roots 768#64 "roots"
  have kept (name : String) (different : ofString "roots"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    bind_lookup_other (PersistentAlloc.post {source with clock:=source.clock-1} roots 768#64) "roots" name roots different
  have away := CopyGeneral.Away.after roots query 768 context.aligned (by have h:=arena.upper; omega) context.below
  exact after_roots_memory entry inner p roots (PersistentAlloc.rounded roots 768#64) out zeros query n ready bounded
    ((kept "p" (by decide)).trans pointer) (bind_lookup_same _ _ _) ((kept "n" (by decide)).trans count)
    ((kept "out" (by decide)).trans output) inputArena arena outArena away outAway returned remaining

/-- Whole current progressive hash: actual allocations and geometric loop,
clear/fold/output/release, real scopes, protected metadata and entering heap. -/
theorem body_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source roots zeros query) (bounded : n≤134217728)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena p (32*n)) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)) := by
  have heap := MarkedHeap.progressive source post roots context.installed context.heap value actual
  rw [prefix_shape.1] at actual
  obtain ⟨positive,inner,remaining,endpoint⟩ := HeapScope.mark_call_trace source post roots "mark" afterMark context.heap
    (HeapScope.mark_original_code source.code context.installed) (some (.returned value)) actual (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" roots
  have kept (name : String) (different : ofString "mark"≠ofString name) := bind_lookup_other {source with clock:=source.clock-1} "mark" name roots different
  have ready : MerkleMemory.Context entry roots zeros query := ⟨context.installed,context.domain,context.zeroCell,context.zeroArena,context.heap,
    context.heapLower,context.heapBound,context.aligned,context.below⟩
  have image := after_mark_memory entry inner p roots out zeros query n ready bounded ((kept "p" (by decide)).trans pointer)
    ((kept "n" (by decide)).trans count) ((kept "out" (by decide)).trans output) inputArena outArena outAway value remaining
  refine ⟨?_,heap⟩
  rw [endpoint]
  exact image

theorem call_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p roots out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source roots zeros query) (bounded : n≤134217728)
    (inputArena : AllocatedBytes.Arena p (32*n)) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p (BitVec.ofNat 64 n) out))
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "merkleize_progressive") arguments)=(none,post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word roots)) := by
  obtain ⟨callee,called,pointer,count,output⟩ := environment source.code.lookup p (BitVec.ofNat 64 n) out (original_code source.code context.installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (ofString "merkleize_progressive") arguments actual
  have valuesEq := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have image := body_frame (callEntryStateHOLFinite source callee) target p roots out zeros query n (context.at_callee callee)
    bounded pointer count output inputArena outArena outAway returned bodyRun
  rw [endpoint]
  exact image

end InitECandidate.Solver.Input.CurrentHash.ProgressiveMemory

#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveMemory.loop_suffix_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveMemory.initialized_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveMemory.after_roots_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveMemory.after_mark_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveMemory.body_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.ProgressiveMemory.call_frame
