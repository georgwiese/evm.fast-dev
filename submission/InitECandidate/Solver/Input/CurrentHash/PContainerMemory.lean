import InitECandidate.Solver.Input.CurrentHash.PContainerMemorySuffix
import InitECandidate.Solver.Input.CurrentHash.PContainerCost
import InitECandidate.Solver.Input.CurrentHash.ProgressiveMemory
import InitECandidate.Solver.Input.CurrentHash.MemoryContextAllocation
import InitECandidate.Solver.Input.CurrentHash.MarkedHeap

namespace InitECandidate.Solver.Input.CurrentHash.PContainer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_tmp_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch tmp cursor out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (short : n≤256) (data : Params source ch n)
    (temporary : source.locals.lookup (ofString "tmp")=some (.val (.word tmp)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena ch (32*n)) (arena : AllocatedBytes.Arena tmp 64) (aligned : tmp.toNat%8=0)
    (tmpAway : CopyGeneral.Away tmp query 64) (outAway : CopyGeneral.Away out query 32) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source afterTmp=(some (.returned value),post)) : post.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) progressiveArguments=some (Progressive.values ch (BitVec.ofNat 64 n) tmp) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,progressiveArguments,localVar,data.chunks,data.count,temporary,Progressive.values,CallNormal.tripleValues]
  have safe : LocalPrefix (ofString "tmp") (.call (some (none,none)) (ofString "merkleize_progressive") progressiveArguments) := .call none _ _ (by intro name impossible; cases impossible)
  rw [body_shape.2.2.1] at actual
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have image := ProgressiveMemory.call_frame source middle ch cursor tmp zeros query n context (by omega) inputArena
    (AllocatedBytes.Arena.weaken tmp 64 32 arena (by decide)) (by intro offset inside; exact tmpAway offset (by omega)) progressiveArguments args normal
  have kept (name : String) := CallNormal.ignored_lookup source middle (ofString name) (ofString "merkleize_progressive") progressiveArguments normal
  have fields := evaluation_fields source middle _ none normal
  have installed : OriginalCode.Installed middle.code := by rw [fields.2.2.2]; exact context.installed
  exact (after_progressive_memory middle post tmp out query n short installed (fields.1.trans context.domain)
    ((kept "tmp").trans temporary) ((kept "n").trans data.count) ((kept "out").trans output) arena aligned tmpAway outAway value remaining).trans image.1

theorem after_mark_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch tmp out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source tmp zeros query) (short : n≤256) (data : Params source ch n)
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena ch (32*n)) (outAway : CopyGeneral.Away out query 32) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [body_shape.2.1] at actual
  apply MemoryContextAllocation.scope_memory source post tmp 64#64 zeros query context "tmp" [.const 64#64] afterTmp rfl _ value actual
  intro inner ready arena returned remaining
  let entry := MemoryContextAllocation.entry source tmp 64#64 "tmp"
  have kept (name : String) (different : ofString "tmp"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    bind_lookup_other (PersistentAlloc.post {source with clock:=source.clock-1} tmp 64#64) "tmp" name tmp different
  have next : Params entry ch n := ⟨(kept "ch" (by decide)).trans data.chunks,(kept "n" (by decide)).trans data.count⟩
  have away := CopyGeneral.Away.after tmp query 64 context.aligned (by have h:=arena.upper; omega) context.below
  exact after_tmp_memory entry inner ch tmp (PersistentAlloc.rounded tmp 64#64) out zeros query n ready short next (bind_lookup_same _ _ _)
    ((kept "out" (by decide)).trans output) inputArena arena context.aligned away outAway returned remaining

/-- Complete actual container hash for the real callers' bounded field counts.
Its normal allocation derives room; metadata and entering heap survive. -/
theorem body_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch tmp out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source tmp zeros query) (short : n≤256) (data : Params source ch n)
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inputArena : AllocatedBytes.Arena ch (32*n)) (outAway : CopyGeneral.Away out query 32) (value : ValueHOL 64)
    (actual : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word tmp)) := by
  have heap := MarkedHeap.pcontainer source post tmp context.installed context.heap value actual
  rw [body_shape.1] at actual
  obtain ⟨positive,inner,remaining,endpoint⟩ := HeapScope.mark_call_trace source post tmp "mark" afterMark context.heap
    (HeapScope.mark_original_code source.code context.installed) (some (.returned value)) actual (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" tmp
  have kept (name : String) (different : ofString "mark"≠ofString name) := bind_lookup_other {source with clock:=source.clock-1} "mark" name tmp different
  have ready : MerkleMemory.Context entry tmp zeros query := ⟨context.installed,context.domain,context.zeroCell,context.zeroArena,context.heap,
    context.heapLower,context.heapBound,context.aligned,context.below⟩
  have next : Params entry ch n := ⟨(kept "ch" (by decide)).trans data.chunks,(kept "n" (by decide)).trans data.count⟩
  have image := after_mark_memory entry inner ch tmp out zeros query n ready short next ((kept "out" (by decide)).trans output) inputArena outAway value remaining
  refine ⟨?_,heap⟩
  rw [endpoint]
  exact image

theorem call_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch tmp out zeros query : BitVec 64) (n : Nat)
    (context : MerkleMemory.Context source tmp zeros query) (short : n≤256)
    (inputArena : AllocatedBytes.Arena ch (32*n)) (outAway : CopyGeneral.Away out query 32) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some [.val (.word ch),.val (.word (BitVec.ofNat 64 n)),.val (.word out)])
    (actual : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_pcontainer") expressions)=(none,post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word tmp)) := by
  obtain ⟨callee,called,chunks,count,output⟩ := word_triple_environment source.code.lookup (ofString "htr_pcontainer")
    (ofString "ch") (ofString "n") (ofString "out") body .one ch (BitVec.ofNat 64 n) out (by decide) (by decide) (by decide) (original_code source.code context.installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ :=
    CallNormal.ignored_data source post (ofString "htr_pcontainer") expressions actual
  have valuesEq := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have image := body_frame (callEntryStateHOLFinite source callee) target ch tmp out zeros query n (context.at_callee callee) short ⟨chunks,count⟩ output inputArena outAway returned bodyRun
  rw [endpoint]
  exact image

end InitECandidate.Solver.Input.CurrentHash.PContainer

#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.after_tmp_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.after_mark_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.body_frame
#print axioms InitECandidate.Solver.Input.CurrentHash.PContainer.call_frame
