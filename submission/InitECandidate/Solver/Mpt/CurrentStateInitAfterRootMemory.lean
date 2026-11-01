import InitECandidate.Solver.Mpt.WitnessMaterializeRichOutput
import InitECandidate.Solver.Mpt.CurrentStateInitWorkspaceContext
import InitECandidate.Solver.Mpt.CurrentStateInitMemoryTail
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Mpt.StateInit.MemorySuffix
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

set_option maxRecDepth 100000 in
theorem entry_shape : afterRoot=.seq (.store (field "ws" 24) (localVar "root"))
    (.decCall (ofString "t") .one (ofString "htab_new") [.const 32#64,.const 64#64] afterTable) ∧
    afterTable=.seq (.store (field "ws" 32) (localVar "t")) (.seq (allocate "bs" [.const 80#64]) afterBlockAllocation) := by
  simp only [afterBlockAllocation,afterTable,afterRoot,rootCall,afterSecond,afterFirst,afterAllocation,body,
    Guest.Software.guestFn_state_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,allocate,field,localVar]
  trivial

/-- The observed workspace store derives its real memory effect and
retains the actual continuation; no mapping or future write is assumed. -/
theorem workspace_store_trace_effect (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws : BitVec 64)
    (context : WorkspaceContext source frontier ws) (offset : Nat) (inside : offset≤32) (expression : ExpHOL 64) (word : BitVec 64)
    (read : eval source expression=some (.val (.word word))) (continuation : ProgHOL 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.seq (.store (field "ws" offset) expression) continuation)=(some (.returned value),post)) :
    ∃ middle,WorkspaceContext middle frontier ws ∧ PersistentMemoryFrame source middle frontier ∧
      middle.memory=StoreWord.put source.memory (ws+BitVec.ofNat 64 offset) word ∧ middle.globals=source.globals ∧
      evaluateHOLFiniteState middle continuation=(some (.returned value),post) := by
  have safe : LocalPrefix (ofString "_") (.store (field "ws" offset) expression):=.store _ _
  obtain ⟨middle,firstRun,continued,preserved⟩:=safe.normal_continue source post continuation value normal
  have addressRead : eval source (field "ws" offset)=some (.val (.word (ws+BitVec.ofNat 64 offset))) := by
    simp [eval,field,evalHOLExact,evalListHOLExact,context.wsCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have number:=byteAddress_toNat ws offset (by have upper:=context.wsFresh.2; omega)
  change (ws+BitVec.ofNat 64 offset).toNat=ws.toNat+offset at number
  obtain ⟨current,first⟩:=context.word_store (field "ws" offset) expression _ word addressRead read (by rw [number]; have lower:=context.wsFresh.1; omega) firstRun
  obtain ⟨mapped,endpoint⟩:=word_store_normal source middle _ _ _ _ addressRead read firstRun
  exact ⟨middle,current,first,(by rw [endpoint] <;> rfl),(by rw [endpoint]),continued⟩

theorem workspace_store_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws : BitVec 64)
    (context : WorkspaceContext source frontier ws) (offset : Nat) (inside : offset≤32) (expression : ExpHOL 64) (word : BitVec 64)
    (read : eval source expression=some (.val (.word word))) (continuation : ProgHOL 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.seq (.store (field "ws" offset) expression) continuation)=(some (.returned value),post)) :
    ∃ middle,WorkspaceContext middle frontier ws ∧ PersistentMemoryFrame source middle frontier ∧
      evaluateHOLFiniteState middle continuation=(some (.returned value),post) := by
  obtain ⟨middle,current,frame,memory,globals,continued⟩:=workspace_store_trace_effect source post frontier ws context offset inside expression word read continuation value normal
  exact ⟨middle,current,frame,continued⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The real BS allocation starts at the entering heap after the WS32
store. The whole following suffix protects that heap prefix, apart from
this one observed workspace word update. -/
theorem after_table_complete_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws table heap : BitVec 64)
    (context : WorkspaceContext source frontier ws)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterTable=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ BlockTables.Complete post frontier ws heap ∧ PersistentMemoryFrame source post frontier ∧
      BlockTables.KeyBuffer post heap ∧ ∀ query : BitVec 64,query.toNat<heap.toNat→query≠ws+32#64→post.memory query=source.memory query := by
  have tableRead : eval source (localVar "t")=some (.val (.word table)):=by simp [eval,evalHOLExact,localVar,toExact,tableCell]
  rw [entry_shape.2] at normal
  obtain ⟨stored,current,first,storedMemory,storedGlobals,continued⟩:=workspace_store_trace_effect source post frontier ws context 32 (by decide) (localVar "t") table tableRead _ value normal
  have safe : LocalPrefix (ofString "_") (allocate "bs" [.const 80#64]):=.globalCall _ _ _
  obtain ⟨allocated,allocRun,tailRun,preserved⟩:=safe.normal_continue stored post afterBlockAllocation value continued
  obtain ⟨bs,tailContext,second,oldHeap,allocatedMemory⟩:=current.allocate_block_exact allocRun
  have actualHeap : stored.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [storedGlobals]; exact heapCell
  have same : bs=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (oldHeap.symm.trans actualHeap)))
  subst bs
  obtain ⟨answer,finalArena,last⟩:=after_block_allocation_frame frontier ws heap allocated post tailContext value tailRun
  obtain ⟨tablesAnswer,next,tables,keyBuffer⟩:=BlockTables.after_block_allocation_tables_key tailContext value tailRun
  have prior:=last.weaken allocated post heap frontier tailContext.bsFresh.1
  have middle:=first.trans source stored allocated frontier frontier second (Nat.le_refl _)
  refine ⟨answer,⟨next,tables⟩,middle.trans source allocated post frontier frontier prior (Nat.le_refl _),keyBuffer,?_⟩
  intro query before away
  exact (last.memory query before).trans ((congrFun allocatedMemory query).trans (by rw [storedMemory]; exact if_neg away))

/-- Both actual workspace stores precede the root's allocation band. The
scoped table/BS allocations advance its real entering heap, and the full
suffix protects every older root word and the newly stored WS24 pointer. -/
theorem after_root_complete_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws node : BitVec 64)
    (context : WorkspaceContext source frontier ws)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word node))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterRoot=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ heap bs,
      source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ heap.toNat≤bs.toNat ∧
      BlockTables.Complete post frontier ws bs ∧ PersistentMemoryFrame source post frontier ∧
      BlockTables.KeyBuffer post bs ∧ post.memory (ws+24#64)=.word node ∧
      ∀ query : BitVec 64,query.toNat<heap.toNat→query≠ws+24#64→query≠ws+32#64→post.memory query=source.memory query := by
  have rootRead : eval source (localVar "root")=some (.val (.word node)):=by simp [eval,evalHOLExact,localVar,toExact,rootCell]
  rw [entry_shape.1] at normal
  obtain ⟨stored,current,first,storedMemory,storedGlobals,continued⟩:=workspace_store_trace_effect source post frontier ws context 24 (by decide) (localVar "root") node rootRead _ value normal
  obtain ⟨heap,heapCell,heapArena,heapBound,heapAligned,before⟩:=current.heap
  have sourceHeap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [←storedGlobals]; exact heapCell
  obtain ⟨callee,called,keyLocal,capLocal⟩:=word_pair_environment stored.code.lookup (ofString "htab_new")
    (ofString "key_len") (ofString "cap") CurrentTable.New.body .one 32#64 64#64 (by decide) (CurrentTable.New.original_code stored.code current.arena.code)
  obtain ⟨funded,target,answer,inner,bodyRun,checked,tailRun,endpoint⟩:=CallNormal.scoped_normal stored post "t" .one (ofString "htab_new")
    [.const 32#64,.const 64#64] _ CurrentTable.New.body afterTable callee .one rfl called value continued
  obtain ⟨answerEq,tableArena,physical⟩:=CurrentTable.New.body_scalar_normal_frame (callEntryStateHOLFinite stored callee) target heap 32#64 64#64 keyLocal capLocal
    (by decide) heapCell heapArena heapBound heapAligned (current.arena.of_frame rfl) answer bodyRun
  rw [answerEq] at tailRun
  let ready:=CallNormal.continuationEntry stored target "t" (.val (.word heap))
  have callerFrame : PersistentNormalFrame stored ready heap:=physical.of_erase _ _ stored ready heap rfl rfl
  have tailContext:=current.after_persistent callerFrame before heapCell
  have tableCell : ready.locals.lookup (ofString "t")=some (.val (.word heap)):=CallNormal.continuation_lookup_same _ _ _ _
  obtain ⟨next,nextCell,nextArena,nextBound,nextAligned,grows⟩:=callerFrame.nextHeap
  obtain ⟨valueEq,records,last,keyBuffer,lastMemory⟩:=after_table_complete_frame ready inner frontier ws heap next tailContext nextCell tableCell value tailRun
  have second:=callerFrame.memory_frame.weaken stored ready heap frontier before
  have middle:=first.trans source stored ready frontier frontier second (Nat.le_refl _)
  have total:=middle.trans source ready inner frontier frontier last (Nat.le_refl _)
  have ws24 : (ws+24#64).toNat=ws.toNat+24:=byteAddress_toNat ws 24 (by have upper:=context.wsArena.upper; omega)
  have ws32 : (ws+32#64).toNat=ws.toNat+32:=byteAddress_toNat ws 32 (by have upper:=context.wsArena.upper; omega)
  have afterWs : ws.toNat+40≤heap.toNat:=by
    obtain ⟨actual,cell,lower,upper,aligned⟩:=current.afterWs
    have same : actual=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (cell.symm.trans heapCell)))
    subst actual
    exact lower
  have pointerCell : inner.memory (ws+24#64)=.word node:=by
    have away : ws+24#64≠ws+32#64:=by intro equal; have numeric:=congrArg BitVec.toNat equal; rw [ws24,ws32] at numeric; omega
    rw [lastMemory (ws+24#64) (by rw [ws24]; omega) away,callerFrame.memory (ws+24#64) (by rw [ws24]; omega),storedMemory]
    exact if_pos rfl
  refine ⟨valueEq,heap,next,sourceHeap,grows,?_,?_,?_,?_,?_⟩
  · rw [endpoint]
    exact records.of_erase rfl
  · exact total.of_erase source inner source post frontier rfl (by rw [endpoint]; rfl)
  · exact keyBuffer.of_erase (by rw [endpoint]; rfl)
  · rw [endpoint]
    exact pointerCell
  · intro query upper away24 away32
    rw [endpoint]
    exact (lastMemory query (Nat.lt_of_lt_of_le upper grows) away32).trans ((callerFrame.memory query upper).trans (by rw [storedMemory]; exact if_neg away24))


theorem after_table_complete (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws table : BitVec 64)
    (context : WorkspaceContext source frontier ws)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterTable=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ bs,BlockTables.Complete post frontier ws bs ∧ PersistentMemoryFrame source post frontier := by
  obtain ⟨heap,cell,owned,bounded,aligned,before⟩:=context.heap
  obtain ⟨answer,complete,frame,keyBuffer,memory⟩:=after_table_complete_frame source post frontier ws table heap context cell tableCell value normal
  exact ⟨answer,heap,complete,frame⟩

/-- Complete actual afterRoot normal suffix, including both workspace
stores, the first scoped table, block-record allocation and all later state
initialization. Normal allocator returns derive every required heap room. -/
theorem after_root_complete (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws node : BitVec 64)
    (context : WorkspaceContext source frontier ws)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word node))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterRoot=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ bs,BlockTables.Complete post frontier ws bs ∧ PersistentMemoryFrame source post frontier := by
  obtain ⟨answer,heap,bs,cell,grows,complete,frame,keyBuffer,pointer,memory⟩:=after_root_complete_frame source post frontier ws node context rootCell value normal
  exact ⟨answer,bs,complete,frame⟩

theorem after_table_context (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws table : BitVec 64)
    (context : WorkspaceContext source frontier ws)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterTable=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ bs,MemoryContext post frontier ws bs ∧ PersistentMemoryFrame source post frontier := by
  obtain ⟨answer,bs,complete,frame⟩:=after_table_complete source post frontier ws table context tableCell value normal
  exact ⟨answer,bs,BlockTables.Complete.memory complete,frame⟩

theorem after_root_context (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws node : BitVec 64)
    (context : WorkspaceContext source frontier ws)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word node))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterRoot=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ bs,MemoryContext post frontier ws bs ∧ PersistentMemoryFrame source post frontier := by
  obtain ⟨answer,bs,complete,frame⟩:=after_root_complete source post frontier ws node context rootCell value normal
  exact ⟨answer,bs,BlockTables.Complete.memory complete,frame⟩

/-- Compatibility projections retain the established earlier-memory API. -/
theorem after_table_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws table : BitVec 64)
    (context : WorkspaceContext source frontier ws)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterTable=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ CurrentStartup.ArenaState post ∧ PersistentMemoryFrame source post frontier := by
  obtain ⟨answer,bs,physical,frame⟩:=after_table_context source post frontier ws table context tableCell value normal
  exact ⟨answer,physical.arena,frame⟩

theorem after_root_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws node : BitVec 64)
    (context : WorkspaceContext source frontier ws)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word node))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterRoot=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ CurrentStartup.ArenaState post ∧ PersistentMemoryFrame source post frontier := by
  obtain ⟨answer,bs,physical,frame⟩:=after_root_context source post frontier ws node context rootCell value normal
  exact ⟨answer,physical.arena,frame⟩

end InitECandidate.Solver.Mpt.StateInit.MemorySuffix

#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.entry_shape
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.after_table_memory
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.after_root_memory

#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.after_table_context
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.after_root_context

#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.after_table_complete
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.after_root_complete

#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.workspace_store_trace_effect


#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.after_table_complete_frame
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.after_root_complete_frame

namespace InitECandidate.Solver.Mpt.StateInit
open Input Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Actual fully initialized records plus the same decoded workspace root,
closed node graph and bounded values. Every node precedes the BS record. -/
structure WorldState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs : BitVec 64) : Prop where
  tables : MemorySuffix.BlockTables.Complete source ws ws bs
  world : ∃ db node,db.toNat≤ws.toNat ∧ source.memory (ws+24#64)=.word node ∧
    ∃ registry : WitnessCore.NodeRegistry source (ws.toNat+40) bs db,registry.graph.valid node

theorem WorldState.memory {source : PanSemStateFiniteExact 64 Guest.HostMemory} {ws bs : BitVec 64}
    (state : WorldState source ws bs) : MemoryContext source ws ws bs:=state.tables.memory

theorem WorldState.at_heap {source : PanSemStateFiniteExact 64 Guest.HostMemory} {ws bs heap : BitVec 64}
    (state : WorldState source ws bs) (cell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) :
    MemorySuffix.BlockTables.Images source bs heap MemorySuffix.BlockTables.specs ∧
      MemorySuffix.BlockTables.Separated source bs MemorySuffix.BlockTables.specs:=state.tables.at_heap cell

/-- Caller scope/clock restoration retains the actual root registry and
initialized tables, independently of the callee's cleared local bindings. -/
theorem WorldState.of_erase {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {ws bs : BitVec 64}
    (state : WorldState source ws bs) (same : LocalEffects.erase target=LocalEffects.erase source) : WorldState target ws bs := by
  have memory:=LocalEffects.memory_of_erase source target same
  have domain:=congrArg PanSemStateFiniteExact.memaddrs same
  change target.memaddrs=source.memaddrs at domain
  obtain ⟨db,node,dbBefore,cell,registry,member⟩:=state.world
  obtain ⟨graph,validEq,regions,disjoint,⟨values⟩⟩:=registry.graph.after_agreement source target 1024 (ws.toNat+40) bs.toNat (WitnessCore.WitnessValue db)
    registry.values registry.regions registry.disjoint domain (fun _ _=>congrFun memory _) (fun _ _=>congrFun memory _)
  refine ⟨state.tables.of_erase same,db,node,dbBefore,(by rw [memory]; exact cell),⟨graph,values,regions,disjoint⟩,?_⟩
  change graph.valid node
  rw [validEq]
  exact member


/-- The genuine completed node and code database state. The code image and
its decoded bounded rows precede WS and are stored in the actual WS+16 cell. -/
structure CodeWorldState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ws bs : BitVec 64)
    extends WorldState source ws bs : Prop where
  little : source.be=false
  codes : ∃ data : CurrentTable.NodeBuild.Data,CurrentTable.NodeLookup.Database source data 65536 ∧
    data.lower=2701135464 ∧ data.lower≤data.table.toNat ∧
    source.memory (ws+16#64)=.word data.table ∧ (CurrentTable.New.endPointer data.table data.cap).toNat≤ws.toNat
  keyBuffer : MemorySuffix.BlockTables.KeyBuffer source bs

theorem CodeWorldState.memory {source : PanSemStateFiniteExact 64 Guest.HostMemory} {ws bs : BitVec 64}
    (state : CodeWorldState source ws bs) : MemoryContext source ws ws bs:=state.toWorldState.memory

theorem CodeWorldState.at_heap {source : PanSemStateFiniteExact 64 Guest.HostMemory} {ws bs heap : BitVec 64}
    (state : CodeWorldState source ws bs) (cell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) :
    MemorySuffix.BlockTables.Images source bs heap MemorySuffix.BlockTables.specs ∧
      MemorySuffix.BlockTables.Separated source bs MemorySuffix.BlockTables.specs:=state.toWorldState.at_heap cell

theorem CodeWorldState.of_erase {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {ws bs : BitVec 64}
    (state : CodeWorldState source ws bs) (same : LocalEffects.erase target=LocalEffects.erase source) : CodeWorldState target ws bs := by
  have memory:=LocalEffects.memory_of_erase source target same
  obtain ⟨data,database,lower,ordered,cell,before⟩:=state.codes
  exact ⟨state.toWorldState.of_erase same,(MemoryMetadata.endian (MemoryMetadata.of_frame same)).trans state.little,
    ⟨data,database.of_frame same,lower,ordered,by rw [memory]; exact cell,before⟩,state.keyBuffer.of_erase same⟩

end InitECandidate.Solver.Mpt.StateInit

namespace InitECandidate.Solver.Mpt.StateInit.MemorySuffix
open Input Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The completed root produced by the actual materializer survives both
workspace stores, scoped table/BS allocation and the whole initializer tail.
The real node regions derive every needed memory-preservation condition. -/
theorem after_root_world (data : CurrentTable.NodeBuild.Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ws node : BitVec 64) (rootLower : Nat) (context : WorkspaceContext source ws ws)
    (databaseBefore : data.table.toNat≤ws.toNat) (output : WitnessMaterialize.RichOutput data rootLower data.table source (.val (.word node)))
    (lower : ws.toNat+40≤rootLower)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word node))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterRoot=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ bs,WorldState post ws bs ∧ PersistentMemoryFrame source post ws ∧
      BlockTables.KeyBuffer post bs ∧ post.memory (ws+16#64)=source.memory (ws+16#64) := by
  obtain ⟨answer,heap,bs,heapCell,grows,complete,frame,keyBuffer,rootWord,memory⟩:=after_root_complete_frame source post ws ws node context rootCell value normal
  obtain ⟨actualHeap,child,valueEq,actualCell,registry,member⟩:=output.2
  have sameHeap : actualHeap=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
  subst actualHeap
  have sameChild : child=node:=HolWordLab.word.inj (ValueHOL.val.inj valueEq.symm)
  subst child
  have domain : post.memaddrs=source.memaddrs:=complete.memory.arena.domain.trans context.arena.domain.symm
  have ws24 : (ws+24#64).toNat=ws.toNat+24:=byteAddress_toNat ws 24 (by have upper:=context.wsArena.upper; omega)
  have ws32 : (ws+32#64).toNat=ws.toNat+32:=byteAddress_toNat ws 32 (by have upper:=context.wsArena.upper; omega)
  have agree : ∀ query,registry.graph.Footprint query→post.memory query=source.memory query:=by
    intro query required
    have bounds:=registry.graph.footprint_bounds rootLower heap.toNat registry.regions query required
    apply memory query bounds.2
    · intro same
      have number:=congrArg BitVec.toNat same
      rw [ws24] at number
      omega
    · intro same
      have number:=congrArg BitVec.toNat same
      rw [ws32] at number
      omega
  have valueAgree : ∀ query,TrieWalk.ValueFootprint registry.graph query→post.memory query=source.memory query:=by
    intro query required
    have bounds:=registry.graph.value_bounds rootLower heap.toNat registry.regions query required
    apply memory query bounds.2
    · intro same
      have number:=congrArg BitVec.toNat same
      rw [ws24] at number
      omega
    · intro same
      have number:=congrArg BitVec.toNat same
      rw [ws32] at number
      omega
  obtain ⟨graph,validEq,regions,disjoint,⟨values⟩⟩:=registry.graph.after_agreement source post 1024 rootLower heap.toNat (WitnessCore.WitnessValue data.table)
    registry.values registry.regions registry.disjoint domain agree valueAgree
  let current : WitnessCore.NodeRegistry post (ws.toNat+40) bs data.table:=
    ⟨graph,values,regions.weaken graph rootLower heap.toNat (ws.toNat+40) bs.toNat lower grows,disjoint⟩
  have currentMember : current.graph.valid node:=by change graph.valid node; rw [validEq]; exact member
  refine ⟨answer,bs,⟨complete,data.table,node,databaseBefore,rootWord,current,currentMember⟩,frame,keyBuffer,?_⟩
  obtain ⟨cursor,cursorCell,afterWs,cursorBound,cursorAligned⟩:=context.afterWs
  have cursorEq : cursor=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (cursorCell.symm.trans heapCell)))
  subst cursor
  have ws16 : (ws+16#64).toNat=ws.toNat+16:=byteAddress_toNat ws 16 (by have bound:=context.wsArena.upper; omega)
  apply memory (ws+16#64) (by rw [ws16]; omega)
  · intro same
    have number:=congrArg BitVec.toNat same
    rw [ws16,ws24] at number
    omega
  · intro same
    have number:=congrArg BitVec.toNat same
    rw [ws16,ws32] at number
    omega

end InitECandidate.Solver.Mpt.StateInit.MemorySuffix

#print axioms InitECandidate.Solver.Mpt.StateInit.WorldState.memory
#print axioms InitECandidate.Solver.Mpt.StateInit.WorldState.at_heap
#print axioms InitECandidate.Solver.Mpt.StateInit.WorldState.of_erase
#print axioms InitECandidate.Solver.Mpt.StateInit.MemorySuffix.after_root_world

#print axioms InitECandidate.Solver.Mpt.StateInit.CodeWorldState.memory
#print axioms InitECandidate.Solver.Mpt.StateInit.CodeWorldState.at_heap
#print axioms InitECandidate.Solver.Mpt.StateInit.CodeWorldState.of_erase
