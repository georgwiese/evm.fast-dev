import InitECandidate.Solver.Mpt.CurrentIndexedStep
import InitECandidate.Solver.Mpt.IndexedPrefixCost
import InitECandidate.Solver.Input.HeapScopeCost
import InitECandidate.Solver.Input.CurrentStartup.ArenaState
import InitECandidate.Solver.Input.ScopedCallNone
import InitECandidate.Solver.Input.ClockCostScopedReached
import InitECandidate.Solver.Input.ClockCostCurrentLoop
import InitECandidate.Solver.Input.LoopNormalExit
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Mpt.CurrentIndexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString QueryBranch Input

/-- One actual current indexed iteration, including both helper callers,
failed writes/allocations and short clocks. -/
theorem iteration_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m array : BitVec 64}
    {count cutoff limit : Nat} {slices : Nat→BitVec 64×BitVec 64} {property : BitVec 64→BitVec 64→Prop}
    (model : LoopModel source m array count cutoff limit slices property) (inside : model.index.toNat<count) :
    source.clock-(evaluateHOLFiniteState source Indexed.loopBody).2.clock≤36826 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) Indexed.keyArguments=
      some [.val (.word keyPointer),.val (.word model.index)]:=by
    simp [Indexed.keyArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,model.keyGlobal,model.indexCell]
  obtain ⟨callee,called,d,w⟩:=RlpWrite.WordWrite.environment source.code.lookup keyPointer model.index (CurrentRlp.WordWrite.original_code source.code model.installed)
  have keyPrice:=CurrentRlp.WordWrite.body_cost (callEntryStateHOLFinite source callee) keyPointer model.index model.installed d w
  by_cases zero : source.clock=0
  · simp only [zero,Nat.zero_sub,Nat.zero_le]
  · have suffix (child : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
        (normal : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) CurrentRlp.WordWrite.body=(some (.returned returned),child))
        (checked : (shapeEqHOL (shapeOfHOLExact returned) .one && shapeEqHOL (shapeOfHOLExact returned) .one)=true) :
        child.clock-(evaluateHOLFiniteState (CallNormal.continuationEntry source child "klen" returned) (.seq Indexed.setCall Indexed.advance)).2.clock≤36807:=by
      let current:=CallNormal.continuationEntry source child "klen" returned
      have reached : CallPrefix.Reaches source (.scoped (ofString "klen") .one (ofString "rlp_encode_word") Indexed.keyArguments) current:=
        .scoped source (ofString "klen") .one (ofString "rlp_encode_word") Indexed.keyArguments _ CurrentRlp.WordWrite.body callee .one returned child args called zero normal checked
      obtain ⟨encoded,next,lower,upper,lengthCell,indexEq,rootEq,heapEq,price⟩:=key_model model reached
      have active : next.index.toNat<count:=by rw [indexEq]; exact inside
      exact ClockCost.sequence_current current Indexed.setCall Indexed.advance 36807 0 (set_cost next upper lengthCell active)
        (ClockCost.of_quiet current.code _ (QuietClock.assign current.code _ _))
    rw [Indexed.loop_body_shape]
    exact ClockCost.scoped_reached_current source "klen" .one (ofString "rlp_encode_word") Indexed.keyArguments _ CurrentRlp.WordWrite.body
      (.seq Indexed.setCall Indexed.advance) callee .one 18 36807 args called keyPrice suffix

/-- The same actual normal iteration advances its true counter once and
retains the complete model, nonheap globals and all original older words. -/
theorem iteration_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {m array : BitVec 64}
    {count cutoff limit : Nat} {slices : Nat→BitVec 64×BitVec 64} {property : BitVec 64→BitVec 64→Prop}
    (model : LoopModel source m array count cutoff limit slices property) (inside : model.index.toNat<count)
    (normal : evaluateHOLFiniteState source Indexed.loopBody=(none,target)) :
    ∃ next : LoopModel target m array count cutoff limit slices property,next.index=model.index+1#64 ∧ model.heap.toNat≤next.heap.toNat ∧
      HeapGlobals source target ∧ (∀ query : BitVec 64,2701134824≤query.toNat→query.toNat<m.toNat→target.memory query=source.memory query) ∧ next.root≠0#64 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) Indexed.keyArguments=
      some [.val (.word keyPointer),.val (.word model.index)]:=by
    simp [Indexed.keyArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,model.keyGlobal,model.indexCell]
  obtain ⟨callee,called,d,w⟩:=RlpWrite.WordWrite.environment source.code.lookup keyPointer model.index (CurrentRlp.WordWrite.original_code source.code model.installed)
  rw [Indexed.loop_body_shape] at normal
  obtain ⟨funded,child,returned,inner,run,checked,continued,endpoint⟩:=CallNormal.scoped_none source target "klen" .one (ofString "rlp_encode_word") Indexed.keyArguments _
    CurrentRlp.WordWrite.body (.seq Indexed.setCall Indexed.advance) callee .one args called normal
  let current:=CallNormal.continuationEntry source child "klen" returned
  have reached : CallPrefix.Reaches source (.scoped (ofString "klen") .one (ofString "rlp_encode_word") Indexed.keyArguments) current:=
    .scoped source (ofString "klen") .one (ofString "rlp_encode_word") Indexed.keyArguments _ CurrentRlp.WordWrite.body callee .one returned child args called (by omega) run checked
  obtain ⟨encoded,converted,lower,upper,lengthCell,indexEq,rootEq,heapEq,price⟩:=key_model model reached
  obtain ⟨middle,setRun,advanceRun⟩:=sequence_none current inner Indexed.setCall Indexed.advance continued
  obtain ⟨updated,updatedIndex,grows,globals,memory,rootPositive⟩:=set_model converted upper lengthCell (by rw [indexEq]; exact inside) setRun
  have sameIndex : updated.index=model.index:=updatedIndex.trans indexEq
  have advanceRead : eval middle (.op .add [localVar "i",.const 1#64])=some (.val (.word (updated.index+1#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,updated.indexCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have executed:=StateSteps.assign_execute middle "i" (.op .add [localVar "i",.const 1#64]) updated.index (updated.index+1#64) updated.indexCell advanceRead
  have innerEq : inner=bind middle "i" (updated.index+1#64):=congrArg Prod.snd (advanceRun.symm.trans executed)
  let final:=restore source "klen" (bind middle "i" (updated.index+1#64))
  have number : (updated.index+1#64).toNat=updated.index.toNat+1:=by
    rw [BitVec.toNat_add_of_lt (by change updated.index.toNat+1<2^64; rw [sameIndex]; have small:=model.countBound; omega)]
    rfl
  have nextBound : (updated.index+1#64).toNat≤count:=by rw [number,sameIndex]; omega
  have iCell : final.locals.lookup (ofString "i")=some (.val (.word (updated.index+1#64))):=
    (restore_lookup_other source _ "klen" "i" (by decide)).trans (bind_lookup_same _ _ _)
  have saved (name : String) (notIndex : ofString "i"≠ofString name) (notLength : ofString "klen"≠ofString name) :
      final.locals.lookup (ofString name)=middle.locals.lookup (ofString name):=
    (restore_lookup_other source _ "klen" name (Ne.symm notLength)).trans (bind_lookup_other _ "i" name _ notIndex)
  obtain ⟨next,nextIndex,nextRoot,nextHeap⟩:=updated.of_frame (target:=final) (updated.index+1#64) nextBound rfl iCell
    ((saved "n" (by decide) (by decide)).trans updated.countCell) ((saved "m" (by decide) (by decide)).trans updated.mCell)
    ((saved "slice_arr" (by decide) (by decide)).trans updated.arrayCell)
  obtain ⟨_encoded,_lower,_upper,_cell,_saved,_price,keyFrame,keyMemory⟩:=key_returned model.index model.installed model.keyGlobal model.indexCell reached
  have keyGlobals:=congrArg PanSemStateFiniteExact.globals keyFrame
  change current.globals=source.globals at keyGlobals
  have totalGrows : model.heap.toNat≤next.heap.toNat:=by
    rw [nextHeap]
    have sameHeap : model.heap=converted.heap:=heapEq.symm
    exact Nat.le_trans (by rw [sameHeap]) grows
  rw [endpoint,innerEq]
  refine ⟨next,?_,totalGrows,?_,?_,by rwa [nextRoot]⟩
  · rw [nextIndex,sameIndex]
  · intro name other
    exact (globals name other).trans (congrArg (fun table=>table.lookup name) keyGlobals)
  · intro query above before
    exact (memory query above before).trans (keyMemory query (Or.inr above))

def loopRank (count : Nat) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Nat:=
  count-(CounterFlow.counterWord source (ofString "i")).toNat

theorem rank_model {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m array : BitVec 64}
    {count cutoff limit : Nat} {slices : Nat→BitVec 64×BitVec 64} {property : BitVec 64→BitVec 64→Prop}
    (model : LoopModel source m array count cutoff limit slices property) : loopRank count source=count-model.index.toNat := by
  simp [loopRank,CounterFlow.counterWord,model.indexCell,valueWord]

theorem active_of_test {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m array : BitVec 64}
    {count cutoff limit : Nat} {slices : Nat→BitVec 64×BitVec 64} {property : BitVec 64→BitVec 64→Prop}
    (model : LoopModel source m array count cutoff limit slices property) (word : BitVec 64)
    (read : eval source Indexed.test=some (.val (.word word))) (nonzero : word≠0#64) : model.index.toNat<count := by
  by_contra inactive
  have expected:=Indexed.test_read source model.index count model.countBound model.indexCell model.countCell
  rw [if_neg inactive] at expected
  have zero : word=0#64:=by
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
  exact nonzero zero

/-- Every original repeated-loop outcome is priced by the actual remaining
unsigned row count. Normal continued iterations increment the real counter;
failed iterations require no future loop state. -/
theorem loop_cost_ranked {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m array : BitVec 64}
    {count cutoff limit : Nat} {slices : Nat→BitVec 64×BitVec 64} {property : BitVec 64→BitVec 64→Prop}
    (model : LoopModel source m array count cutoff limit slices property) :
    source.clock-(evaluateHOLFiniteState source (.while Indexed.test Indexed.loopBody)).2.clock≤36827*loopRank count source := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>Nonempty (LoopModel current m array count cutoff limit slices property)
  have priced : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) Indexed.test=some (.val (.word word))→
      word≠0#64→current.clock≠0→current.clock-1-(evaluateHOLFiniteState (decClockHOLFinite current) Indexed.loopBody).2.clock≤36826:=by
    intro current codeEq valid word read nonzero funded
    obtain ⟨live⟩:=valid
    have active:=active_of_test live word read nonzero
    let entered : LoopModel (decClockHOLFinite current) m array count cutoff limit slices property:={live with rows:=live.rows.of_band current (decClockHOLFinite current) array count m.toNat limit slices NonemptyRow rfl (by intros; rfl)}
    exact iteration_cost entered active
  have progress : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) Indexed.test=some (.val (.word word))→word≠0#64→
      0<loopRank count current ∧ (current.clock≠0→let output:=evaluateHOLFiniteState (decClockHOLFinite current) Indexed.loopBody
        (output.1=none ∨ output.1=some .continue)→invariant output.2 ∧ loopRank count output.2<loopRank count current):=by
    intro current codeEq valid word read nonzero
    obtain ⟨live⟩:=valid
    have active:=active_of_test live word read nonzero
    have before:=rank_model live
    refine ⟨by rw [before]; omega,?_⟩
    intro funded
    dsimp only
    intro continuing
    let output:=evaluateHOLFiniteState (decClockHOLFinite current) Indexed.loopBody
    have normal : output.1=none:=by
      rcases continuing with normal|continued
      · exact normal
      · exact ((Indexed.loop_body_limit.summary_full (decClockHOLFinite current)).2.2.2 continued).elim
    have run : evaluateHOLFiniteState (decClockHOLFinite current) Indexed.loopBody=(none,output.2):=Prod.ext normal rfl
    let entered : LoopModel (decClockHOLFinite current) m array count cutoff limit slices property:={live with rows:=live.rows.of_band current (decClockHOLFinite current) array count m.toNat limit slices NonemptyRow rfl (by intros; rfl)}
    obtain ⟨next,nextIndex,grows,globals,memory,_positive⟩:=iteration_normal entered active run
    have number : (live.index+1#64).toNat=live.index.toNat+1:=by
      rw [BitVec.toNat_add_of_lt (by change live.index.toNat+1<2^64; have small:=live.countBound; omega)]
      rfl
    have nextNumber : next.index.toNat=live.index.toNat+1:=(congrArg BitVec.toNat nextIndex).trans number
    refine ⟨⟨next⟩,?_⟩
    rw [rank_model next,nextNumber,before]
    omega
  exact ClockCost.ranked_loop_current source.code Indexed.test Indexed.loopBody 36826 invariant (loopRank count) priced progress source rfl ⟨model⟩

theorem loop_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m array : BitVec 64}
    {count cutoff limit : Nat} {slices : Nat→BitVec 64×BitVec 64} {property : BitVec 64→BitVec 64→Prop}
    (model : LoopModel source m array count cutoff limit slices property) :
    source.clock-(evaluateHOLFiniteState source (.while Indexed.test Indexed.loopBody)).2.clock≤36827*count := by
  exact Nat.le_trans (loop_cost_ranked model) (Nat.mul_le_mul_left 36827 (by rw [rank_model model]; omega))

/-- A successful complete loop checked every original row, retains all
older caller words and nonheap globals, and supplies its final real graph. -/
theorem loop_normal {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {m array : BitVec 64}
    {count cutoff limit : Nat} {slices : Nat→BitVec 64×BitVec 64} {property : BitVec 64→BitVec 64→Prop}
    (model : LoopModel source m array count cutoff limit slices property)
    (normal : evaluateHOLFiniteState source (.while Indexed.test Indexed.loopBody)=(none,post)) :
    ∃ final : LoopModel post m array count cutoff limit slices property,final.index.toNat=count ∧ model.heap.toNat≤final.heap.toNat ∧
      HeapGlobals source post ∧ (∀ query : BitVec 64,2701134824≤query.toNat→query.toNat<m.toNat→post.memory query=source.memory query) ∧
      ((model.root≠0#64 ∨ model.index.toNat<count) → final.root≠0#64) := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>∃ live : LoopModel current m array count cutoff limit slices property,
    model.heap.toNat≤live.heap.toNat ∧ HeapGlobals source current ∧
      (∀ query : BitVec 64,2701134824≤query.toNat→query.toNat<m.toNat→current.memory query=source.memory query) ∧
      ((model.root≠0#64 ∨ model.index.toNat<live.index.toNat) → live.root≠0#64)
  have initial : invariant source:=⟨model,Nat.le_refl _,by intro name other; rfl,by intros; rfl,by intro incoming; exact incoming.elim id (fun impossible=>(Nat.lt_irrefl _ impossible).elim)⟩
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ word : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) Indexed.test=some (.val (.word word))→
      word≠0#64→current.clock≠0→∀ target,evaluateHOLFiniteState (decClockHOLFinite current) Indexed.loopBody=(none,target)→invariant target:=by
    intro current codeEq valid word read nonzero funded target bodyRun
    obtain ⟨live,grows,globals,memory,positive⟩:=valid
    let entered : LoopModel (decClockHOLFinite current) m array count cutoff limit slices property:={live with rows:=live.rows.of_band current (decClockHOLFinite current) array count m.toNat limit slices NonemptyRow rfl (by intros; rfl)}
    obtain ⟨next,nextIndex,nextGrows,nextGlobals,nextMemory,nextPositive⟩:=iteration_normal entered (active_of_test live word read nonzero) bodyRun
    exact ⟨next,Nat.le_trans grows nextGrows,fun name other=>(nextGlobals name other).trans (globals name other),
      fun query above before=>(nextMemory query above before).trans (memory query above before),fun _=>nextPositive⟩
  obtain ⟨final,grows,globals,memory,positive⟩:=loop_invariant_no_control source.code Indexed.test Indexed.loopBody
    (fun current=>(Indexed.loop_body_limit.summary_full current).2.2) invariant step source post rfl initial normal
  have exited:=loop_normal_exit Indexed.test Indexed.loopBody (fun current=>(Indexed.loop_body_limit.summary_full current).2.2.1) source post normal
  have expected:=Indexed.test_read post final.index count final.countBound final.indexCell final.countCell
  have exactCount : final.index.toNat=count:=by
    by_cases active : final.index.toNat<count
    · rw [if_pos active] at expected
      have impossible : (0#64 : BitVec 64)=1#64:=by
        simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using exited.symm.trans expected
      exact False.elim ((by decide : (0#64 : BitVec 64)≠1#64) impossible)
    · have bounded:=final.bounded
      omega
  exact ⟨final,exactCount,grows,globals,memory,by simpa only [exactCount] using positive⟩

/-- Uniform current transaction-count specialization. This is only the
repeated-loop allowance, separate from setup/root and target instructions. -/
theorem loop_uniform {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m array : BitVec 64}
    {count cutoff limit : Nat} {slices : Nat→BitVec 64×BitVec 64} {property : BitVec 64→BitVec 64→Prop}
    (model : LoopModel source m array count cutoff limit slices property) (countBound : count≤12582752) :
    source.clock-(evaluateHOLFiniteState source (.while Indexed.test Indexed.loopBody)).2.clock≤463385007904 := by
  have priced:=loop_cost model
  omega

/-- Physical current builder entry. The older real rows are nonempty and
owned, and its exact scalar ABI and startup key global are already reached.
No constructor, loop or final root success is an entry premise. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64)
    (count : Nat) (out : BitVec 64) (limit : Nat) (slices : Nat→BitVec 64×BitVec 64)
    (property : BitVec 64→BitVec 64→Prop := fun _ _=>True) where
  heap : BitVec 64
  arrayCell : source.locals.lookup (ofString "slice_arr")=some (.val (.word array))
  countCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))
  outCell : source.locals.lookup (ofString "out")=some (.val (.word out))
  countBound : count<2^64
  domain : source.memaddrs=InitE.ordinaryDomain
  little : source.be=false
  installed : OriginalCode.Installed source.code
  keyGlobal : source.globals.lookup (ofString "mpt_key_scratch")=some (.val (.word keyPointer))
  heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapArena : AllocatedBytes.Arena heap 0
  heapAligned : heap.toNat%8=0
  heapAbove : 2701134824≤heap.toNat
  rows : Indexed.SliceArray source array count heap.toNat limit slices NonemptyRow
  rowValues : ∀ index<count,property (slices index).1 (slices index).2
  emptyValue : property 0#64 0#64

/-- The actual three prefix actions derive a fresh empty header and its
loop model at the genuine post-allocation heap. Its own room comes from
the real constructor return extracted from this execution. -/
theorem Entry.setup {source current : PanSemStateFiniteExact 64 Guest.HostMemory} {array out : BitVec 64}
    {count limit : Nat} {slices : Nat→BitVec 64×BitVec 64} {property : BitVec 64→BitVec 64→Prop}
    (data : Entry source array count out limit slices property) (execution : CallPrefix.Execution source Indexed.actions current) :
    ∃ cutoff,Nonempty (LoopModel current data.heap array count cutoff limit slices property) ∧
      current.clock=source.clock-3 ∧
      (∀ query : BitVec 64,query.toNat<data.heap.toNat→current.memory query=source.memory query) ∧ HeapGlobals source current ∧
      current.locals.lookup (ofString "out")=source.locals.lookup (ofString "out") ∧
      current.locals.lookup (ofString "mark")=some (.val (.word data.heap)) := by
  obtain ⟨arena,currentEq⟩:=Indexed.setup_from_execution source current data.heap data.installed data.heapCell data.domain data.heapArena data.heapAligned execution
  have heapUpper:=Indexed.setup_heap_upper source current data.heap data.installed data.heapCell data.domain
    data.heapArena data.heapAligned execution
  rw [currentEq]
  let ready:=Indexed.loopEntry source data.heap
  obtain ⟨heapCell,heapArena,aligned,grows⟩:=Indexed.loop_entry_heap source data.heap arena
  let heap:=PersistentAlloc.rounded data.heap 16#64
  let cutoff:=heap.toNat
  let graph:=TrieWalk.Graph.empty ready.memory ready.memaddrs
  obtain ⟨mCell,indexCell⟩:=Indexed.loop_entry_locals source data.heap
  have saved (name : String) (notMark : ofString "mark"≠ofString name) (notMap : ofString "m"≠ofString name) (notIndex : ofString "i"≠ofString name) :
      ready.locals.lookup (ofString name)=source.locals.lookup (ofString name):=Indexed.loop_entry_saved source data.heap _ notMark notMap notIndex
  have globals:=Indexed.loop_entry_globals source data.heap
  obtain ⟨rootStored,flagStored⟩:=Indexed.loop_entry_cells source data.heap arena
  have older (query : BitVec 64) (before : query.toNat<data.heap.toNat) : ready.memory query=source.memory query:=
    Indexed.loop_entry_older source data.heap query arena before
  let model : LoopModel ready data.heap array count cutoff limit slices property:={
    index:=0#64,root:=0#64,heap:=heap,indexCell:=indexCell
    countCell:=(saved "n" (by decide) (by decide) (by decide)).trans data.countCell
    mCell:=mCell,arrayCell:=(saved "slice_arr" (by decide) (by decide) (by decide)).trans data.arrayCell
    bounded:=by simp,countBound:=data.countBound,domain:=data.domain,little:=data.little,installed:=data.installed
    keyGlobal:=(globals _ (by decide)).trans data.keyGlobal,heapCell:=heapCell,heapArena:=heapArena,heapAligned:=aligned,heapUpper:=heapUpper,floor:=Nat.le_refl _
    headerArena:=arena,headerAligned:=data.heapAligned,headerAbove:=data.heapAbove,headerBefore:=grows,cutoffAligned:=aligned
    rootStored:=rootStored,flagStored:=flagStored
    rows:=data.rows.of_band source ready array count data.heap.toNat limit slices NonemptyRow rfl (fun query above before=>older query before)
    rowValues:=data.rowValues,emptyValue:=data.emptyValue
    graph:=graph,member:=rfl,rootUncached:=Or.inl rfl,rootNonHash:=by intro impossible; exact (impossible rfl).elim
    values:=TrieWalk.Values.empty ready.memory ready.memaddrs limit property
    regions:=TrieWalk.Graph.Regions.empty ready.memory ready.memaddrs cutoff cutoff
    disjoint:=TrieWalk.Graph.Disjoint.empty ready.memory ready.memaddrs
    paths:=TrieWalk.Graph.PathBytes.empty ready.memory ready.memaddrs ready.be
    pathRegions:=TrieWalk.Graph.PathRegions.empty ready.memory ready.memaddrs cutoff cutoff
    separated:=TrieWalk.Graph.PathSeparated.empty ready.memory ready.memaddrs }
  exact ⟨cutoff,⟨model⟩,Indexed.loop_entry_clock source data.heap,older,globals,
    saved "out" (by decide) (by decide) (by decide),Indexed.loop_entry_mark source data.heap⟩

/-- Every builder outcome stops in its complete prefix allowance or reaches
the actual initialized loop with the same original continuation. -/
theorem to_loop {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {array out : BitVec 64}
    {count limit : Nat} {slices : Nat→BitVec 64×BitVec 64} {property : BitVec 64→BitVec 64→Prop}
    (data : Entry source array count out limit slices property) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source Indexed.body=(outcome,post)) :
    (source.clock-post.clock≤4 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ current inner cutoff,Nonempty (LoopModel current data.heap array count cutoff limit slices property) ∧
        current.clock≤source.clock ∧ source.clock-current.clock≤4 ∧ post.clock=inner.clock ∧
        evaluateHOLFiniteState current Indexed.loopAndAfter=(outcome,inner) ∧
        (∀ query : BitVec 64,query.toNat<data.heap.toNat→current.memory query=source.memory query) ∧ HeapGlobals source current ∧
        current.locals.lookup (ofString "out")=source.locals.lookup (ofString "out") ∧
        current.locals.lookup (ofString "mark")=some (.val (.word data.heap)) := by
  rcases Indexed.prefix_trace source post data.installed outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨current,inner,execution,forward,price,endpoint,remaining⟩:=reached
    obtain ⟨cutoff,model,clock,memory,globals,outCell,markCell⟩:=data.setup execution
    exact Or.inr ⟨current,inner,cutoff,model,forward,price,endpoint,remaining,memory,globals,outCell,markCell⟩

/-- Complete prefix and repeated loop, priced only through its actual normal
continuation. The final root calculation remains an explicit suffix. -/
theorem to_after_loop_trace {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {array out : BitVec 64}
    {count limit : Nat} {slices : Nat→BitVec 64×BitVec 64} {property : BitVec 64→BitVec 64→Prop}
    (data : Entry source array count out limit slices property) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source Indexed.body=(outcome,post)) :
    (source.clock-post.clock≤36827*count+4 ∧ ∀ value,outcome≠some (.returned value)) ∨ ∃ current inner cutoff,
      (∃ model : LoopModel current data.heap array count cutoff limit slices property,model.index.toNat=count) ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤36827*count+4 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current Indexed.afterLoop=(outcome,inner) ∧ HeapGlobals source current ∧
      (∀ query : BitVec 64,2701134824≤query.toNat→query.toNat<data.heap.toNat→current.memory query=source.memory query) ∧
      current.locals.lookup (ofString "out")=some (.val (.word out)) ∧ current.locals.lookup (ofString "mark")=some (.val (.word data.heap)) := by
  rcases to_loop data outcome run with stopped|reached
  · exact Or.inl ⟨by have price:=stopped.1; omega,stopped.2⟩
  · obtain ⟨entered,inner,cutoff,⟨model⟩,forward,price,endpoint,remaining,older,globals,outEntered,markEntered⟩:=reached
    rw [Indexed.loop_shape,evaluateHOLFiniteState_seq_line780] at remaining
    have loopPrice:=loop_cost model
    have loopForward:=evaluateHOLFiniteState_clock_le entered (.while Indexed.test Indexed.loopBody)
    have loopNever:=((LocalPrefix.loop Indexed.test Indexed.loop_body_limit).summary_full entered).2.1
    generalize computed : evaluateHOLFiniteState entered (.while Indexed.test Indexed.loopBody)=output at loopPrice loopForward loopNever remaining
    obtain ⟨result,current⟩:=output
    change entered.clock-current.clock≤36827*count at loopPrice
    change current.clock≤entered.clock at loopForward
    cases result with
    | none=>
      obtain ⟨next,finished,grows,nextGlobals,nextMemory,_positive⟩:=loop_normal model computed
      exact Or.inr ⟨current,inner,cutoff,⟨next,finished⟩,Nat.le_trans loopForward forward,by omega,endpoint,remaining,
        fun name other=>(nextGlobals name other).trans (globals name other),
        (fun query above before=>(nextMemory query above before).trans (older query before)),
        (Indexed.loop_saved entered current (ofString "out") (by decide) (by decide) computed).trans (outEntered.trans data.outCell),
        (Indexed.loop_saved entered current (ofString "mark") (by decide) (by decide) computed).trans markEntered⟩
    | some result=>
      have clocks:=congrArg (fun output=>output.2.clock) remaining
      change current.clock=inner.clock at clocks
      refine Or.inl ⟨by rw [endpoint,←clocks]; omega,?_⟩
      intro value returned
      apply loopNever value
      have observed:=congrArg Prod.fst remaining
      change some result=outcome at observed
      exact observed.trans returned


/-- Existing projection; the stronger trace also excludes a returned
body in its stopped branch, as required by an enclosing real caller. -/
theorem to_after_loop {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {array out : BitVec 64}
    {count limit : Nat} {slices : Nat→BitVec 64×BitVec 64} {property : BitVec 64→BitVec 64→Prop}
    (data : Entry source array count out limit slices property) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source Indexed.body=(outcome,post)) :
    source.clock-post.clock≤36827*count+4 ∨ ∃ current inner cutoff,
      (∃ model : LoopModel current data.heap array count cutoff limit slices property,model.index.toNat=count) ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤36827*count+4 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current Indexed.afterLoop=(outcome,inner) ∧ HeapGlobals source current ∧
      (∀ query : BitVec 64,2701134824≤query.toNat→query.toNat<data.heap.toNat→current.memory query=source.memory query) ∧
      current.locals.lookup (ofString "out")=some (.val (.word out)) ∧ current.locals.lookup (ofString "mark")=some (.val (.word data.heap)) := by
  rcases to_after_loop_trace data outcome run with stopped|reached
  · exact Or.inl stopped.1
  · exact Or.inr reached

/-- Earlier startup supplies the actual empty-root buffer global; the
payload header supplies its owned output. These physical facts are separate
from the fresh-row entry and contain no successful future call premise. -/
structure RootInputs (source : PanSemStateFiniteExact 64 Guest.HostMemory) (out empty : BitVec 64) : Prop where
  arena : CurrentStartup.ArenaState source
  emptyGlobal : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word empty))
  emptyArena : AllocatedBytes.Arena empty 32
  outArena : AllocatedBytes.Arena out 32


end InitECandidate.Solver.Mpt.CurrentIndexed

#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.iteration_cost
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.iteration_normal

#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.loop_cost_ranked
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.loop_cost
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.loop_normal

#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.loop_uniform

#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.Entry.setup
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.to_loop
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.to_after_loop

#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.to_after_loop_trace
