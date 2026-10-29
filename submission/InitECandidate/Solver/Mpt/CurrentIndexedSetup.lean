import InitECandidate.Solver.Mpt.CurrentIndexedLoop
import InitECandidate.Solver.Mpt.IndexedPrefixCost

namespace InitECandidate.Solver.Mpt.CurrentIndexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString QueryBranch Input

/-- Physical current builder entry. The older real rows are nonempty and
owned, and its exact scalar ABI and startup key global are already reached.
No constructor, loop or final root success is an entry premise. -/
structure Entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64)
    (count : Nat) (out : BitVec 64) (limit : Nat) (slices : Nat→BitVec 64×BitVec 64) where
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

/-- The actual three prefix actions derive a fresh empty header and its
loop model at the genuine post-allocation heap. Its own room comes from
the real constructor return extracted from this execution. -/
theorem Entry.setup {source current : PanSemStateFiniteExact 64 Guest.HostMemory} {array out : BitVec 64}
    {count limit : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (data : Entry source array count out limit slices) (execution : CallPrefix.Execution source Indexed.actions current) :
    ∃ cutoff,Nonempty (LoopModel current data.heap array count cutoff limit slices) ∧
      current.clock=source.clock-3 ∧
      (∀ query : BitVec 64,query.toNat<data.heap.toNat→current.memory query=source.memory query) ∧ HeapGlobals source current := by
  obtain ⟨arena,currentEq⟩:=Indexed.setup_from_execution source current data.heap data.installed data.heapCell data.domain data.heapArena data.heapAligned execution
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
  let model : LoopModel ready data.heap array count cutoff limit slices:={
    index:=0#64,root:=0#64,heap:=heap,indexCell:=indexCell
    countCell:=(saved "n" (by decide) (by decide) (by decide)).trans data.countCell
    mCell:=mCell,arrayCell:=(saved "slice_arr" (by decide) (by decide) (by decide)).trans data.arrayCell
    bounded:=by simp,countBound:=data.countBound,domain:=data.domain,little:=data.little,installed:=data.installed
    keyGlobal:=(globals _ (by decide)).trans data.keyGlobal,heapCell:=heapCell,heapArena:=heapArena,heapAligned:=aligned,floor:=Nat.le_refl _
    headerArena:=arena,headerAligned:=data.heapAligned,headerAbove:=data.heapAbove,headerBefore:=grows,cutoffAligned:=aligned
    rootStored:=rootStored,flagStored:=flagStored
    rows:=data.rows.of_band source ready array count data.heap.toNat limit slices NonemptyRow rfl (fun query above before=>older query before)
    graph:=graph,member:=rfl,values:=TrieWalk.Values.empty ready.memory ready.memaddrs limit (fun _ _=>True)
    regions:=TrieWalk.Graph.Regions.empty ready.memory ready.memaddrs cutoff cutoff
    disjoint:=TrieWalk.Graph.Disjoint.empty ready.memory ready.memaddrs
    paths:=TrieWalk.Graph.PathBytes.empty ready.memory ready.memaddrs ready.be
    pathRegions:=TrieWalk.Graph.PathRegions.empty ready.memory ready.memaddrs cutoff cutoff
    separated:=TrieWalk.Graph.PathSeparated.empty ready.memory ready.memaddrs }
  exact ⟨cutoff,⟨model⟩,Indexed.loop_entry_clock source data.heap,older,globals⟩

/-- Every builder outcome stops in its complete prefix allowance or reaches
the actual initialized loop with the same original continuation. -/
theorem to_loop {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {array out : BitVec 64}
    {count limit : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (data : Entry source array count out limit slices) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source Indexed.body=(outcome,post)) :
    (source.clock-post.clock≤4 ∧ ∀ value,outcome≠some (.returned value)) ∨
      ∃ current inner cutoff,Nonempty (LoopModel current data.heap array count cutoff limit slices) ∧
        current.clock≤source.clock ∧ source.clock-current.clock≤4 ∧ post.clock=inner.clock ∧
        evaluateHOLFiniteState current Indexed.loopAndAfter=(outcome,inner) ∧
        (∀ query : BitVec 64,query.toNat<data.heap.toNat→current.memory query=source.memory query) ∧ HeapGlobals source current := by
  rcases Indexed.prefix_trace source post data.installed outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨current,inner,execution,forward,price,endpoint,remaining⟩:=reached
    obtain ⟨cutoff,model,clock,memory,globals⟩:=data.setup execution
    exact Or.inr ⟨current,inner,cutoff,model,forward,price,endpoint,remaining,memory,globals⟩

/-- Complete prefix and repeated loop, priced only through its actual normal
continuation. The final root calculation remains an explicit suffix. -/
theorem to_after_loop {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {array out : BitVec 64}
    {count limit : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (data : Entry source array count out limit slices) (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source Indexed.body=(outcome,post)) :
    source.clock-post.clock≤36827*count+4 ∨ ∃ current inner cutoff,
      (∃ model : LoopModel current data.heap array count cutoff limit slices,model.index.toNat=count) ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤36827*count+4 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current Indexed.afterLoop=(outcome,inner) ∧ HeapGlobals source current ∧
      (∀ query : BitVec 64,2701134824≤query.toNat→query.toNat<data.heap.toNat→current.memory query=source.memory query) := by
  rcases to_loop data outcome run with stopped|reached
  · exact Or.inl (by have price:=stopped.1; omega)
  · obtain ⟨entered,inner,cutoff,⟨model⟩,forward,price,endpoint,remaining,older,globals⟩:=reached
    rw [Indexed.loop_shape,evaluateHOLFiniteState_seq_line780] at remaining
    have loopPrice:=loop_cost model
    have loopForward:=evaluateHOLFiniteState_clock_le entered (.while Indexed.test Indexed.loopBody)
    generalize computed : evaluateHOLFiniteState entered (.while Indexed.test Indexed.loopBody)=output at loopPrice loopForward remaining
    obtain ⟨result,current⟩:=output
    change entered.clock-current.clock≤36827*count at loopPrice
    change current.clock≤entered.clock at loopForward
    cases result with
    | none=>
      obtain ⟨next,finished,grows,nextGlobals,nextMemory⟩:=loop_normal model computed
      exact Or.inr ⟨current,inner,cutoff,⟨next,finished⟩,Nat.le_trans loopForward forward,by omega,endpoint,remaining,
        fun name other=>(nextGlobals name other).trans (globals name other),
        fun query above before=>(nextMemory query above before).trans (older query before)⟩
    | some result=>
      have clocks:=congrArg (fun output=>output.2.clock) remaining
      change current.clock=inner.clock at clocks
      exact Or.inl (by rw [endpoint,←clocks]; omega)

end InitECandidate.Solver.Mpt.CurrentIndexed

#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.Entry.setup
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.to_loop
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.to_after_loop
