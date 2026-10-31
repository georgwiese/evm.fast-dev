import InitECandidate.Solver.Mpt.CurrentIndexedLoop
import InitECandidate.Solver.Mpt.IndexedPrefixCost
import InitECandidate.Solver.Mpt.CurrentTrieRoot
import InitECandidate.Solver.Input.HeapReleaseNormal

namespace InitECandidate.Solver.Mpt.CurrentIndexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString QueryBranch Input

def rootArguments : List (ExpHOL 64):=[localVar "m",localVar "out"]
def rootCall : ProgHOL 64:=.call (some (none,none)) (ofString "mpt_root") rootArguments
def releaseArguments : List (ExpHOL 64):=[localVar "mark"]
def releaseCall : ProgHOL 64:=.call (some (none,none)) (ofString "heap_release") releaseArguments

set_option maxRecDepth 100000 in
theorem after_loop_shape : Indexed.afterLoop=.seq rootCall (.seq releaseCall (.return (.const 0#64))) := by
  simp only [Indexed.afterLoop,Indexed.loopAndAfter,Indexed.afterNew,Indexed.afterMark,Indexed.body,Guest.guestFn_build_mpt_indexed,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,rootCall,rootArguments,releaseCall,releaseArguments,localVar]

/-- Retain the actual initialized hash workspace when only the persistent
heap global changes. No memory contents or future hash return are required. -/
theorem hash_environment {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (environment : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64)
    (domain : target.memaddrs=source.memaddrs) (code : OriginalCode.Installed target.code)
    (globals : HeapGlobals source target) :
    CurrentKeccak.Hash.Environment target 2701132160#64 2701132360#64 := {
  installed:=code
  domain:=domain.trans environment.domain
  stateGlobal:=(globals _ (by decide)).trans environment.stateGlobal
  padGlobal:=(globals _ (by decide)).trans environment.padGlobal
  stateArena:=environment.stateArena,padArena:=environment.padArena
  stateAligned:=environment.stateAligned,padAligned:=environment.padAligned }

/-- The indexed loop's actual retained graph, heap, paths and borrowed
values supply serialization. Cached counts need only their stored word type. -/
def LoopModel.persistent {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m array : BitVec 64}
    {count cutoff limit inputEnd : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (model : LoopModel source m array count cutoff limit slices (InputValue inputEnd))
    (environment : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64)
    (inputBefore : inputEnd≤cutoff) (valueFits : limit+19≤2^63) :
    NodeRlpFill.Persistent source model.heap cutoff model.heap.toNat inputEnd (2^64-1) limit := {
  graph:=model.graph,regions:=model.regions,disjoint:=model.disjoint,values:=model.values
  paths:=model.paths,pathRegions:=model.pathRegions,separated:=model.separated
  ordered:=model.floor,lowerAligned:=model.cutoffAligned,beforeHeap:=Nat.le_refl _
  heapCell:=model.heapCell,heapLower:=by have lower:=model.heapArena.lower; exact lower
  heapUpper:=model.heapUpper,heapAligned:=model.heapAligned
  stp:=2701132160#64,pad:=2701132360#64,environment:=environment
  stateBefore:=by have a:=model.headerAbove; have b:=model.headerBefore; change 2701132360≤cutoff; omega
  padBefore:=by have a:=model.headerAbove; have b:=model.headerBefore; change 2701132496≤cutoff; omega
  inputBeforeNodes:=inputBefore,stateBeforeInput:=by decide,padBeforeInput:=by decide
  cached:=NodeRlpFinish.cached_lengths_word_limit model.graph,valueFits:=valueFits }

theorem RootInputs.after_heap {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {out empty : BitVec 64}
    (roots : RootInputs source out empty) (domain : target.memaddrs=source.memaddrs)
    (code : OriginalCode.Installed target.code) (globals : HeapGlobals source target) : RootInputs target out empty := {
  arena:=⟨(globals _ (by decide)).trans roots.arena.scratch,(globals _ (by decide)).trans roots.arena.frame,
    domain.trans roots.arena.domain,code⟩
  emptyGlobal:=(globals _ (by decide)).trans roots.emptyGlobal
  emptyArena:=roots.emptyArena,outArena:=roots.outArena }

theorem RootInputs.scratch {source : PanSemStateFiniteExact 64 Guest.HostMemory} {out empty : BitVec 64}
    (roots : RootInputs source out empty) : Rlp.Validation.Arena source 2965299200#64 2952790016#64 :=
  ⟨roots.arena.domain,roots.arena.scratch,roots.arena.frame,by decide,by decide,by decide,by decide⟩

theorem LoopModel.header_mapped {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m array : BitVec 64}
    {count cutoff limit : Nat} {slices : Nat→BitVec 64×BitVec 64} {property : BitVec 64→BitVec 64→Prop}
    (model : LoopModel source m array count cutoff limit slices property) : source.memaddrs m := by
  simpa only [byteAddress,BitVec.add_zero] using
    AllocatedBytes.word_mapped source m 16 0 model.domain model.headerArena (by decide) model.headerAligned (by decide)

/-- The real root call handles every nonempty indexed root. Its kind is
provided by actual insertion, rather than an empty-root conclusion. -/
theorem root_call_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {m array out empty : BitVec 64}
    {count cutoff limit inputEnd protectedEnd : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (model : LoopModel source m array count cutoff limit slices (InputValue inputEnd)) (roots : RootInputs source out empty)
    (environment : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64)
    (inputBefore : inputEnd≤cutoff) (valueFits : limit+19≤2^63)
    (outAligned : out.toNat%8=0) (outputSeparate : out.toNat+32≤2701134824 ∨ protectedEnd≤out.toNat)
    (beforeInput : protectedEnd≤inputEnd)
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (normal : evaluateHOLFiniteState source rootCall=(none,target)) :
    target.locals=source.locals ∧ Nonempty (CurrentTrieRoot.Root.Output source target protectedEnd (.val (.word 0#64))) := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) rootArguments=some [.val (.word m),.val (.word out)]:=by
    simp [rootArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,model.mCell,outCell]
  exact CurrentTrieRoot.Root.call_normal (model.persistent environment inputBefore valueFits) model.member
    (fun active=>Or.inl (model.rootNonHash active)) (Rlp.LiveArena.of_startup roots.arena) roots.scratch
    model.header_mapped model.rootStored (by decide) roots.emptyGlobal roots.outArena outAligned outputSeparate beforeInput rootArguments args normal

/-- Complete real root caller, including aborting and short-clock outcomes. -/
theorem root_call_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m array out empty : BitVec 64}
    {count cutoff limit inputEnd : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (model : LoopModel source m array count cutoff limit slices (InputValue inputEnd)) (roots : RootInputs source out empty)
    (environment : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64)
    (inputBefore : inputEnd≤cutoff) (valueFits : limit+19≤2^63)
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out))) :
    source.clock-(evaluateHOLFiniteState source rootCall).2.clock≤CurrentTrieRoot.Root.bodyPrice (2^64-1) limit+1 := by
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) rootArguments=some [.val (.word m),.val (.word out)]:=by
    simp [rootArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,model.mCell,outCell]
  exact CurrentTrieRoot.Root.call_cost (model.persistent environment inputBefore valueFits) model.member
    (fun active=>Or.inl (model.rootNonHash active)) (Rlp.LiveArena.of_startup roots.arena) roots.scratch
    model.header_mapped model.rootStored (by decide) (some none) rootArguments args

/-- The actual root calculation, heap release and final return are all
priced, including outcomes which stop in either real helper. -/
theorem after_loop_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {m array out empty : BitVec 64}
    {count cutoff limit inputEnd : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (model : LoopModel source m array count cutoff limit slices (InputValue inputEnd)) (roots : RootInputs source out empty)
    (environment : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64)
    (inputBefore : inputEnd≤cutoff) (valueFits : limit+19≤2^63)
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out))) :
    source.clock-(evaluateHOLFiniteState source Indexed.afterLoop).2.clock≤CurrentTrieRoot.Root.bodyPrice (2^64-1) limit+2 := by
  have price:=root_call_cost model roots environment inputBefore valueFits outCell
  have released : ClockCost.Bound source.code releaseCall 1:=HeapScope.release_call_cost source.code model.installed (some none) releaseArguments
  have tail : ClockCost.Bound source.code (.seq releaseCall (.return (.const 0#64))) 1:=
    ClockCost.sequence source.code _ _ 1 0 released (ClockCost.returned source.code _)
  rw [after_loop_shape]
  exact ClockCost.sequence_current source rootCall _ (CurrentTrieRoot.Root.bodyPrice (2^64-1) limit+1) 1 price tail

/-- Enlarging the decoded-value frontier and length cap needs only the
corresponding numeric inequalities; it adds no physical entry assumption. -/
def Entry.widen {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array out : BitVec 64}
    {count limit inputEnd nextLimit nextEnd : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (data : Entry source array count out limit slices (InputValue inputEnd))
    (lengthBound : limit≤nextLimit) (endBound : inputEnd≤nextEnd) :
    Entry source array count out nextLimit slices (InputValue nextEnd) := {
  data with
  rows:=by
    refine {data.rows with payload:=?_}
    intro index inside
    obtain ⟨small,fits,mapped⟩:=data.rows.payload index inside
    exact ⟨small.trans lengthBound,fits,mapped⟩
  rowValues:=by
    intro index inside
    obtain ⟨before,above⟩:=data.rowValues index inside
    exact ⟨before.trans endBound,above⟩
  emptyValue:=by simp [InputValue] }

/-- Larger value caps can only enlarge the actual serializer allowance. -/
theorem root_price_mono {cacheLimit small large : Nat} (bound : small≤large) :
    CurrentTrieRoot.Root.bodyPrice cacheLimit small≤CurrentTrieRoot.Root.bodyPrice cacheLimit large := by
  have copied:=NodeRlpFill.copy_price_mono bound
  simp only [CurrentTrieRoot.Root.bodyPrice,CurrentTrieRoot.NodeHash.bodyPrice,NodeRlpFill.bodyPrice,
    NodeRlpFill.stepPrice,NodeRlpFill.choicePrice,NodeRlpFill.finishPrice,NodeRlpFinish.branchAllowance]
  omega

/-- The complete unchanged builder, for empty and nonempty rows. Actual
setup/insertion derive heap and root-kind facts; decoded values supply their
original borrowed interval. No later successful execution is assumed. -/
theorem body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array out empty : BitVec 64}
    {count limit inputEnd : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (data : Entry source array count out limit slices (InputValue inputEnd)) (roots : RootInputs source out empty)
    (environment : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64)
    (inputBefore : inputEnd≤data.heap.toNat) (valueFits : limit+19≤2^63) :
    source.clock-(evaluateHOLFiniteState source Indexed.body).2.clock≤36827*count+CurrentTrieRoot.Root.bodyPrice (2^64-1) limit+6 := by
  let output:=evaluateHOLFiniteState source Indexed.body
  rcases to_after_loop data output.1 rfl with stopped|reached
  · exact Nat.le_trans stopped (by omega)
  · obtain ⟨current,inner,cutoff,⟨model,finished⟩,forward,price,endpoint,remaining,globals,older,outCell,markCell⟩:=reached
    have currentDomain : current.memaddrs=source.memaddrs:=model.domain.trans data.domain.symm
    have currentRoots:=roots.after_heap currentDomain model.installed globals
    have currentEnvironment:=hash_environment environment currentDomain model.installed globals
    have before : inputEnd≤cutoff:=by have header:=model.headerBefore; omega
    have suffix:=after_loop_cost model currentRoots currentEnvironment before valueFits outCell
    have nextClock:=evaluateHOLFiniteState_clock_le current Indexed.afterLoop
    rw [remaining] at suffix nextClock
    change current.clock-inner.clock≤CurrentTrieRoot.Root.bodyPrice (2^64-1) limit+2 at suffix
    change inner.clock≤current.clock at nextClock
    change source.clock-output.2.clock≤36827*count+CurrentTrieRoot.Root.bodyPrice (2^64-1) limit+6
    have clocks : output.2.clock=inner.clock:=endpoint
    rw [clocks]
    omega

/-- Uniform complete source allowance at the current transaction/row caps.
This includes real nonempty serialization and is not a target-step bound. -/
theorem uniform_body_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {array out empty : BitVec 64}
    {count limit inputEnd : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (data : Entry source array count out limit slices (InputValue inputEnd)) (roots : RootInputs source out empty)
    (environment : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64)
    (inputBefore : inputEnd≤data.heap.toNat) (countBound : count≤12582752) (limitBound : limit≤268435456) :
    source.clock-(evaluateHOLFiniteState source Indexed.body).2.clock≤91390403933770582 := by
  have fits : limit+19≤2^63:=by omega
  have price:=body_cost data roots environment inputBefore fits
  have capped:=root_price_mono (cacheLimit:=2^64-1) limitBound
  rw [CurrentTrieRoot.Root.bodyPrice_at_word_limit] at capped
  omega

/-- A real normal builder return restores the saved heap and preserves the
caller's earlier input/header band, for any actual row count. -/
theorem body_normal {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {array out empty : BitVec 64}
    {count limit inputEnd protectedEnd : Nat} {slices : Nat→BitVec 64×BitVec 64}
    (data : Entry source array count out limit slices (InputValue inputEnd)) (roots : RootInputs source out empty)
    (environment : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64)
    (inputBefore : inputEnd≤data.heap.toNat) (valueFits : limit+19≤2^63)
    (outAligned : out.toNat%8=0) (outputSeparate : out.toNat+32≤2701134824 ∨ protectedEnd≤out.toNat)
    (beforeInput : protectedEnd≤inputEnd) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source Indexed.body=(some (.returned value),target)) :
    value=.val (.word 0#64) ∧ target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      target.globals.lookup (ofString "heap_ptr")=some (.val (.word data.heap)) ∧ HeapGlobals source target ∧
      ∀ query : BitVec 64,2701134824≤query.toNat→query.toNat<protectedEnd→target.memory query=source.memory query := by
  rcases Indexed.prefix_trace source target data.installed (some (.returned value)) normal with stopped|reached
  · exact (stopped.2 value rfl).elim
  · obtain ⟨entered,inner,execution,forward,price,endpoint,remaining⟩:=reached
    obtain ⟨cutoff,⟨model⟩,clock,older,globals,outEntered,markEntered⟩:=data.setup execution
    have continued:=remaining
    rw [Indexed.loop_shape] at remaining
    have safe : LocalPrefix (ofString "n") (.while Indexed.test Indexed.loopBody):=.loop Indexed.test Indexed.loop_body_limit
    obtain ⟨current,loopRun,suffixRun⟩:=sequence_returned entered inner (.while Indexed.test Indexed.loopBody) Indexed.afterLoop value
      (fun returned=>(safe.summary_full entered).2.1 returned) remaining
    obtain ⟨final,finished,grows,nextGlobals,nextMemory,positive⟩:=loop_normal model loopRun
    have currentGlobals : HeapGlobals source current:=fun name other=>(nextGlobals name other).trans (globals name other)
    have currentDomain : current.memaddrs=source.memaddrs:=final.domain.trans data.domain.symm
    have currentRoots:=roots.after_heap currentDomain final.installed currentGlobals
    have currentEnvironment:=hash_environment environment currentDomain final.installed currentGlobals
    have before : inputEnd≤cutoff:=by have header:=final.headerBefore; omega
    have outCurrent : current.locals.lookup (ofString "out")=some (.val (.word out)):=
      (Indexed.loop_saved entered current (ofString "out") (by decide) (by decide) loopRun).trans (outEntered.trans data.outCell)
    have markCurrent : current.locals.lookup (ofString "mark")=some (.val (.word data.heap)):=
      (Indexed.loop_saved entered current (ofString "mark") (by decide) (by decide) loopRun).trans markEntered
    rw [after_loop_shape] at suffixRun
    obtain ⟨copied,rootRun,footerRun⟩:=sequence_returned current inner rootCall (.seq releaseCall (.return (.const 0#64))) value
      (fun returned=>NoReturn.ignored_call (ofString "mpt_root") rootArguments current returned) suffixRun
    obtain ⟨copyLocals,⟨copyOutput⟩⟩:=root_call_normal final currentRoots currentEnvironment before valueFits outAligned outputSeparate beforeInput outCurrent rootRun
    have copiedMark : copied.locals.lookup (ofString "mark")=some (.val (.word data.heap)):=by rw [copyLocals]; exact markCurrent
    have rootFields:=evaluation_fields current copied rootCall none rootRun
    have copiedInstalled : OriginalCode.Installed copied.code:=by rw [rootFields.2.2.2]; exact final.installed
    obtain ⟨released,releaseRun,returnRun⟩:=sequence_returned copied inner releaseCall (.return (.const 0#64)) value
      (fun returned=>NoReturn.ignored_call (ofString "heap_release") releaseArguments copied returned) footerRun
    have args : evalListHOLFinite copied (h:=fun query=>Classical.propDecidable (copied.memaddrs query)) releaseArguments=some [.val (.word data.heap)]:=by
      simp [releaseArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,copiedMark]
    have releaseEq:=HeapScope.release_normal copied released data.heap copyOutput.heap releaseArguments args copyOutput.heapCell copiedInstalled releaseRun
    obtain ⟨answer,innerEq⟩:=return_normal released inner (.const 0#64) value returnRun
    have valueEq : value=.val (.word 0#64):=Option.some.inj (answer.symm.trans rfl)
    have finalFrame:=execution.erase Indexed.loopAndAfter
    rw [←Indexed.body_shape,normal,continued,innerEq,releaseEq] at finalFrame
    have finalGlobals:=congrArg PanSemStateFiniteExact.globals finalFrame
    change target.globals=(HeapScope.releasePost copied data.heap).globals at finalGlobals
    have finalMemory:=congrArg PanSemStateFiniteExact.memory finalFrame
    change target.memory=copied.memory at finalMemory
    have fields:=evaluation_fields source target Indexed.body (some (.returned value)) normal
    refine ⟨valueEq,fields.1,fields.2.1,fields.2.2.2,?_,?_,?_⟩
    · rw [finalGlobals]
      simp [HeapScope.releasePost,HolFiniteMapExact.update,FUPDATE]
    · intro name other
      rw [finalGlobals]
      change (copied.globals.update (ofString "heap_ptr",.val (.word data.heap))).lookup name=source.globals.lookup name
      have copyGlobals:=copyOutput.globals name other
      simpa [HolFiniteMapExact.update,FUPDATE,Ne.symm other] using copyGlobals.trans (currentGlobals name other)
    · intro query above inside
      rw [finalMemory]
      exact (copyOutput.input query above inside).trans ((nextMemory query above (by omega)).trans (older query (by omega)))

end InitECandidate.Solver.Mpt.CurrentIndexed

#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.LoopModel.persistent
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.root_call_normal
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.root_call_cost
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.after_loop_cost
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.body_cost

#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.body_normal

#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.Entry.widen
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.root_price_mono
#print axioms InitECandidate.Solver.Mpt.CurrentIndexed.uniform_body_cost
