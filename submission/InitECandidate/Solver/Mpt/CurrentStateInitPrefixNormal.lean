import InitECandidate.Solver.Mpt.StateInitPrefixTrace
import InitECandidate.Solver.Mpt.StateInitPrefixFrame
import InitECandidate.Solver.Mpt.StateInitPrefixFields
import InitECandidate.Solver.Mpt.StateInitRootNormal
import InitECandidate.Solver.Mpt.CurrentStateInitAfterRootMemory

namespace InitECandidate.Solver.Mpt.StateInit
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- An actual enclosing normal return must pass the same real workspace
allocation and stores. Its request room and funding are derived from that
execution; a cheap failed prefix is excluded rather than treated as success. -/
theorem current_root_normal_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap nodes root codes : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (nodesCell : source.locals.lookup (ofString "nodedb")=some (.val (.word nodes)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root)))
    (codesCell : source.locals.lookup (ofString "codedb")=some (.val (.word codes)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    heap.toNat+40≤2952790016 ∧ 1≤source.clock ∧
      evaluateHOLFiniteState (ready source heap nodes root codes) rootCall=(some (.returned value),post) := by
  rw [shapes.1] at normal
  have safe : LocalPrefix (ofString "nodedb") allocate:=.globalCall _ _ _
  obtain ⟨allocatedPost,allocationRun,continued,preserved⟩:=safe.normal_continue source post afterAllocation value normal
  obtain ⟨room,funded,allocatedEq⟩:=PersistentAlloc.global_call_normal_any source allocatedPost "ws" heap 40#64 [.const 40#64] rfl
    (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) heapCell heapUpper allocationRun
  have nodeArena : AllocatedBytes.Arena heap 40:=⟨heapLower,by change heap.toNat+40≤2952790016 at room; omega⟩
  have wsCell : (allocated source heap).globals.lookup (ofString "ws")=some (.val (.word heap)):=putGlobal.lookup_same _ _ _
  have actualStores:=stores_execute (allocated source heap) heap nodes root codes wsCell nodesCell rootCell codesCell domain nodeArena aligned
  rw [allocatedEq] at continued
  change evaluateHOLFiniteState (allocated source heap) afterAllocation=(some (.returned value),post) at continued
  rw [actualStores] at continued
  exact ⟨room,funded,continued⟩

/-- The complete actual initializer returns its allocated workspace/block
records and protects every word before its entering heap. Its restored
scratch cursor and bounded advancing heap come from the observed execution. -/
theorem current_body_normal_context (data : CurrentTable.NodeBuild.Data)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root codes : BitVec 64)
    (database : CurrentTable.NodeLookup.Database source data)
    (tableBefore : (CurrentTable.New.endPointer data.table data.cap).toNat≤heap.toNat)
    (arena : CurrentStartup.ArenaState source)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapUpper : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (nodesCell : source.locals.lookup (ofString "nodedb")=some (.val (.word data.table)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root)))
    (codesCell : source.locals.lookup (ofString "codedb")=some (.val (.word codes)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ bs,MemoryContext post heap heap bs ∧
      WitnessCore.Stack.StablePrefix source post heap.toNat := by
  obtain ⟨room,funded,continued⟩:=current_root_normal_trace source post heap data.table root codes arena.code
    heapCell heapLower heapUpper aligned nodesCell rootCell codesCell arena.domain value normal
  let prepared:=ready source heap data.table root codes
  let next:=PersistentAlloc.rounded heap 40#64
  have checked:=PersistentAlloc.guards heap 40#64 room
  have allocatedExtent : heap.toNat+40≤next.toNat:=checked.2.2.1
  have grows : heap.toNat≤next.toNat:=by omega
  have nextArena : AllocatedBytes.Arena next 0:=⟨by omega,by have upper:=checked.2.2.2.1; change next.toNat≤2952790016 at upper; omega⟩
  have preparedArena:=ready_arena source heap data.table root codes arena
  have preparedFields:=ready_fields source heap data.table root codes
  have preparedDatabase : CurrentTable.NodeLookup.Database prepared data:=database.of_before heap.toNat tableBefore rfl rfl
    (fun query earlier=>ready_memory_before source heap data.table root codes query room earlier)
  have physical : Rlp.Validation.Arena prepared 2965299200#64 2952790016#64:=
    ⟨preparedArena.domain,preparedArena.scratch,preparedArena.frame,by decide,by decide,by decide,by decide⟩
  obtain ⟨current,inner,node,output,nodeCell,priorMemory,codeEq,live,others,tailRun,endpoint,scratchCell⟩:=
    root_call_normal data prepared post next root 2965299200#64 2952790016#64 preparedDatabase
      (tableBefore.trans grows) nodesCell rootCell preparedFields.2.2.1 nextArena checked.2.2.2.1
      checked.2.2.2.2 (Rlp.LiveArena.of_startup preparedArena) physical value continued
  have currentArena : CurrentStartup.ArenaState current:=
    ⟨scratchCell,(others _ (by decide) (by decide)).trans preparedArena.frame,live.domain,live.code⟩
  obtain ⟨last,child,valueEq,lastCell,lastArena,lastBound,lastAligned,lastGrowth,rest⟩:=output
  have currentWorkspace : WorkspaceContext current heap heap:=
    ⟨currentArena,⟨last,lastCell,lastArena,lastBound,lastAligned,grows.trans lastGrowth⟩,
      (others _ (by decide) (by decide)).trans preparedFields.2.1,⟨Nat.le_refl _,heapUpper⟩,
      ⟨heapLower,by omega⟩,aligned,⟨last,lastCell,allocatedExtent.trans lastGrowth,lastBound,lastAligned⟩⟩
  obtain ⟨answer,bs,records,lastFrame⟩:=MemorySuffix.after_root_context current inner heap heap node
    currentWorkspace nodeCell value tailRun
  refine ⟨answer,bs,?_,?_⟩
  · rw [endpoint]
    exact records.of_frame rfl
  · intro query earlier
    rw [endpoint]
    exact (lastFrame.memory query earlier).trans ((priorMemory query (Nat.lt_of_lt_of_le earlier grows)).trans
      (ready_memory_before source heap data.table root codes query room earlier))

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.current_root_normal_trace
#print axioms InitECandidate.Solver.Mpt.StateInit.current_body_normal_context
