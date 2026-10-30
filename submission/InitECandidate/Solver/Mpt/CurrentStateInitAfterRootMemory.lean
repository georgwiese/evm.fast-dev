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
theorem workspace_store_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws : BitVec 64)
    (context : WorkspaceContext source frontier ws) (offset : Nat) (inside : offset≤32) (expression : ExpHOL 64) (word : BitVec 64)
    (read : eval source expression=some (.val (.word word))) (continuation : ProgHOL 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.seq (.store (field "ws" offset) expression) continuation)=(some (.returned value),post)) :
    ∃ middle,WorkspaceContext middle frontier ws ∧ PersistentMemoryFrame source middle frontier ∧
      evaluateHOLFiniteState middle continuation=(some (.returned value),post) := by
  have safe : LocalPrefix (ofString "_") (.store (field "ws" offset) expression):=.store _ _
  obtain ⟨middle,firstRun,continued,preserved⟩:=safe.normal_continue source post continuation value normal
  have addressRead : eval source (field "ws" offset)=some (.val (.word (ws+BitVec.ofNat 64 offset))) := by
    simp [eval,field,evalHOLExact,evalListHOLExact,context.wsCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have number:=byteAddress_toNat ws offset (by have upper:=context.wsFresh.2; omega)
  change (ws+BitVec.ofNat 64 offset).toNat=ws.toNat+offset at number
  obtain ⟨current,first⟩:=context.word_store (field "ws" offset) expression _ word addressRead read (by rw [number]; have lower:=context.wsFresh.1; omega) firstRun
  exact ⟨middle,current,first,continued⟩

theorem after_table_context (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws table : BitVec 64)
    (context : WorkspaceContext source frontier ws)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterTable=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ bs,MemoryContext post frontier ws bs ∧ PersistentMemoryFrame source post frontier := by
  have tableRead : eval source (localVar "t")=some (.val (.word table)):=by simp [eval,evalHOLExact,localVar,toExact,tableCell]
  rw [entry_shape.2] at normal
  obtain ⟨stored,current,first,continued⟩:=workspace_store_trace source post frontier ws context 32 (by decide) (localVar "t") table tableRead _ value normal
  have safe : LocalPrefix (ofString "_") (allocate "bs" [.const 80#64]):=.globalCall _ _ _
  obtain ⟨allocated,allocRun,tailRun,preserved⟩:=safe.normal_continue stored post afterBlockAllocation value continued
  obtain ⟨bs,tailContext,second⟩:=current.allocate_block allocRun
  obtain ⟨valueEq,finalArena,last⟩:=after_block_allocation_frame frontier ws bs allocated post tailContext value tailRun
  have front:=first.trans source stored allocated frontier frontier second (Nat.le_refl _)
  exact ⟨valueEq,bs,finalArena,front.trans source allocated post frontier frontier last (Nat.le_refl _)⟩

/-- Complete actual afterRoot normal suffix, including both workspace
stores, the first scoped table, block-record allocation and all later state
initialization. Normal allocator returns derive every required heap room. -/
theorem after_root_context (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws node : BitVec 64)
    (context : WorkspaceContext source frontier ws)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word node))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterRoot=(some (.returned value),post)) :
    value=.val (.word 0#64) ∧ ∃ bs,MemoryContext post frontier ws bs ∧ PersistentMemoryFrame source post frontier := by
  have rootRead : eval source (localVar "root")=some (.val (.word node)):=by simp [eval,evalHOLExact,localVar,toExact,rootCell]
  rw [entry_shape.1] at normal
  obtain ⟨stored,current,first,continued⟩:=workspace_store_trace source post frontier ws context 24 (by decide) (localVar "root") node rootRead _ value normal
  obtain ⟨heap,heapCell,heapArena,heapBound,heapAligned,before⟩:=current.heap
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
  obtain ⟨valueEq,bs,finalArena,last⟩:=after_table_context ready inner frontier ws heap tailContext tableCell value tailRun
  have second:=callerFrame.memory_frame.weaken stored ready heap frontier before
  have middle:=first.trans source stored ready frontier frontier second (Nat.le_refl _)
  have total:=middle.trans source ready inner frontier frontier last (Nat.le_refl _)
  exact ⟨valueEq,bs,(by rw [endpoint]; exact finalArena.of_frame rfl),total.of_erase source inner source post frontier rfl (by rw [endpoint]; rfl)⟩

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
