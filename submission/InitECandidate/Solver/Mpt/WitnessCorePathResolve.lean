import InitECandidate.Solver.Mpt.WitnessCoreRichResolve
import InitECandidate.Solver.Mpt.WitnessCorePathDatabaseFrame
import InitECandidate.Solver.Mpt.WitnessCorePathRegistryExtend
import InitECandidate.Solver.Mpt.WitnessCorePathRelabel

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix
open Flapjack.Basis.Pure.MlString
open Input.Main.RunAttemptConstructors

/-- A genuine original resolver iteration installs the actual pending
hash and either delivers a fresh result or supplies a bounded next input.
Both alternatives preserve the full invariant and decrease actual rank. -/
theorem PathInvariant.resolve_normal (input : Guest.InputBlob) (frontier : Nat) (db heap cursor limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stack : List Entry)
    (model : PathInvariant input frontier db limit source ⟨heap,cursor,stack,.resolve,true⟩)
    (frontierLower : 2713731432≤frontier)
    (normal : evaluateHOLFiniteState source resolveBranch=(none,post)) :
    ∃ next : Configuration,PathInvariant input frontier db limit post next ∧
      next.rank limit<(Configuration.mk heap cursor stack .resolve true).rank limit := by
  have invariant:=model.base
  obtain ⟨registry,pathModel⟩:=model.registry
  obtain ⟨entry,rest,stackEq,waiting,slotCell⟩:=invariant.phase
  change stack=entry::rest at stackEq
  subst stack
  obtain ⟨oldResult,resultCell⟩:=invariant.words.result
  obtain ⟨oldPointer,pointerCell⟩:=invariant.words.pointer
  obtain ⟨oldLength,lengthCell⟩:=invariant.words.length
  obtain ⟨step,dbCell,goCell,words,frame⟩:=core_resolve_stack_normal input source post db heap cursor limit oldResult oldPointer oldLength 2#64 entry rest
    invariant.view (invariant.boundary input frontier db limit source _) invariant.dbCell invariant.topCell slotCell resultCell pointerCell lengthCell invariant.modeCell
    invariant.heapCell invariant.aligned invariant.scratch invariant.below invariant.heapLower invariant.installed normal
  have frozen:=invariant.frozen.database_frame input source post frontier heap invariant.frontierBefore frame dbCell
  have actualDb:=dbCell.trans invariant.dbCell
  have actualGo:=goCell.trans invariant.goCell
  have installed : Input.OriginalCode.Installed post.code:=by rw [frame.code]; exact invariant.installed
  have above : 2713717616≤frontier := by omega
  have tags:=registry.nodes.tags_database source post frontier heap db above frame
  obtain ⟨next,pending,nextCell,nextArena,aligned,grows,scratch,view,top,slot,shape⟩:=step
  let nextEntry : Entry:={entry with pending:=some pending}
  have fresh : FreshFrom frontier (nextEntry::rest):=invariant.fresh.advance frontier entry nextEntry rest rfl rfl
  have nextWaiting : Waiting (nextEntry::rest):=waiting.cons nextEntry rest ⟨pending,rfl⟩
  have postLittle : post.be=false:=frame.endian.trans model.little
  obtain ⟨oldNodes,validEq⟩:=registry.nodes.after_database_frame source post frontier heap db above frame
  have oldIncludes : ∀ node,registry.nodes.graph.valid node → oldNodes.graph.valid node:=by
    intro node member; rw [validEq]; exact member
  have oldChildren:=registry.children_database source post frontier db _ invariant.view oldNodes.graph oldIncludes frame
  have oldExcludes:=registry.excludes_same source post frontier db _ oldNodes.graph validEq tags
  let oldRegistry : ActiveRegistry post frontier db ⟨heap,cursor,entry::rest,.resolve,true⟩:=
    ⟨oldNodes,oldChildren,oldExcludes,(by intro phase; cases phase)⟩
  have oldPaths : oldRegistry.PathModel:=pathModel.database_frame source post frontier db _ registry oldRegistry validEq invariant.view frontierLower frame
  have oldRecords (current : Entry) (member : current∈entry::rest) : WitnessRecord.View post current.record db current.data:=by
    rcases List.mem_cons.mp member with same|older
    · subst current; exact view.records nextEntry List.mem_cons_self
    · exact view.records current (List.mem_cons_of_mem _ older)
  have oldBounded (current : Entry) (member : current∈entry::rest) : current.data.BeforeHeap heap.toNat:=
    (invariant.view.before current member).mono current.data current.mark heap.toNat (invariant.view.marks current member)
  have mapping (current : Entry) (member : current∈nextEntry::rest) :
      ∃ previous∈entry::rest,current.data.payload.storage=previous.data.payload.storage:=by
    rcases List.mem_cons.mp member with same|older
    · subst current; exact ⟨entry,List.mem_cons_self,rfl⟩
    · exact ⟨current,List.mem_cons_of_mem _ older,rfl⟩
  rcases shape with ⟨zero,node,result,mode,owned,resolved,rank⟩|⟨pointer,length,actualPointer,actualLength,mode,small,lower,before,validHash,rank⟩
  · have parentLower:=invariant.view.marks entry List.mem_cons_self
    have returnedOwned:=owned.weaken post node heap.toNat next.toNat (max frontier (resultLower (nextEntry::rest))) next.toNat
      (max_le invariant.frontierBefore parentLower) (Nat.le_refl _)
    obtain ⟨nodes,nodesPaths,member,includes,members⟩:=registry.nodes.resolve_terminal_paths source post frontier db heap next node
      pathModel.nodes (by omega) invariant.frontierBefore frame grows resolved nextCell scratch.domain invariant.aligned
    have childrenOld:=registry.children_database source post frontier db _ invariant.view nodes.graph includes frame
    have children : ChildViews post nodes.graph.valid (nextEntry::rest) := childrenOld.pending post nodes.graph.valid entry rest pending
    have freshResult : node≠0#64 → heap.toNat≤node.toNat := by intro active; exact (owned.resolve_left active).fresh
    have oldExcluded:=registry.excludes_extension source post frontier db _ invariant.view nodes.graph node members tags freshResult
    have excludes:=excludes_pending post.memory post.memaddrs nodes.graph entry rest pending oldExcluded
    have base : Invariant input frontier db limit post ⟨next,cursor,nextEntry::rest,.returning,true⟩ :=
      ⟨frozen,actualDb,nextCell,nextArena,aligned,invariant.heapLower.trans grows,invariant.frontierBefore.trans grows,
        scratch,invariant.below,view,fresh,words,top,mode,actualGo,⟨nextWaiting,node,result,returnedOwned⟩,Or.inl rfl,installed⟩
    let active : ActiveRegistry post frontier db ⟨next,cursor,nextEntry::rest,.returning,true⟩ := ⟨nodes,children,excludes,by
      intro phase child cell
      have same : child=node := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (cell.symm.trans result)))
      subst child
      exact member⟩
    have hashKind : node=0#64 ∨ wordAt post.memory node=0#64:=by
      rcases resolved with empty|⟨valueEq,arena,stored,hashData,actualHeap,actualCell,finalArena,finalAligned,before⟩|
        ⟨pointer,length,pending,valueEq,small,lower,upper,hashSpan⟩
      · left; simpa [resolveAnswer] using empty
      · right
        have same : node=heap:=by simpa [resolveAnswer] using valueEq
        subst node
        simp [wordAt,stored,MemoryBytes.wordBits]
      · simp [resolveAnswer] at valueEq
    have allocation (nonnull : node≠0#64) : AllocatedBytes.Arena node (TrieWalk.nodeBytes (wordAt post.memory node)):=by
      rw [hashKind.resolve_left nonnull]
      exact (owned.resolve_left nonnull).arena
    have newPath (nonnull : node≠0#64) (tag : wordAt post.memory node=1#64 ∨ wordAt post.memory node=2#64) :
        heap.toNat≤(wordAt post.memory (node+32#64)).toNat ∧ (wordAt post.memory (node+32#64)).toNat%8=0:=by
      rw [hashKind.resolve_left nonnull] at tag
      rcases tag with impossible|impossible <;> cases impossible
    have currentMembers : ∀ owner,nodes.graph.valid owner → oldRegistry.nodes.graph.valid owner ∨ owner=node:=by
      intro owner current
      rcases members owner current with prior|same
      · left; change oldNodes.graph.valid owner; rw [validEq]; exact prior
      · exact Or.inr same
    let built : ActiveRegistry post frontier db ⟨next,cursor,entry::rest,.resolve,true⟩:=
      ⟨nodes,childrenOld,oldExcluded,(by intro phase; cases phase)⟩
    have builtPaths : built.PathModel:=oldPaths.node_added post frontier db _ _ node oldRegistry built nodesPaths rfl oldRecords oldBounded currentMembers freshResult allocation newPath
    have newPaths : active.PathModel:=builtPaths.relabel post frontier db _ _ built active nodesPaths rfl mapping
    exact ⟨⟨next,cursor,nextEntry::rest,.returning,true⟩,⟨base,postLittle,active,newPaths⟩,rank⟩
  · let nodes:=oldNodes.advance_heap post frontier heap next db grows
    have includes : ∀ child,registry.nodes.graph.valid child → nodes.graph.valid child := by
      intro child member; change oldNodes.graph.valid child; rw [validEq]; exact member
    have childrenOld:=registry.children_database source post frontier db _ invariant.view nodes.graph includes frame
    have children : ChildViews post nodes.graph.valid (nextEntry::rest) := childrenOld.pending post nodes.graph.valid entry rest pending
    have oldExcluded:=registry.excludes_same source post frontier db _ nodes.graph validEq tags
    have excludes:=excludes_pending post.memory post.memaddrs nodes.graph entry rest pending oldExcluded
    have base : Invariant input frontier db limit post ⟨next,cursor,nextEntry::rest,.decode,true⟩ :=
      ⟨frozen,actualDb,nextCell,nextArena,aligned,invariant.heapLower.trans grows,invariant.frontierBefore.trans grows,
        scratch,invariant.below,view,fresh,words,top,mode,actualGo,
        ⟨nextWaiting,pointer,length,actualPointer,actualLength,small,lower,before⟩,Or.inl rfl,installed⟩
    let active : ActiveRegistry post frontier db ⟨next,cursor,nextEntry::rest,.decode,true⟩ :=
      ⟨nodes,children,excludes,by intro phase; cases phase⟩
    have nodesPaths : nodes.PathModel:=oldPaths.nodes.advance_heap post frontier heap next db oldNodes grows
    have newPaths : active.PathModel:=oldPaths.relabel post frontier db _ _ oldRegistry active nodesPaths rfl mapping
    exact ⟨⟨next,cursor,nextEntry::rest,.decode,true⟩,⟨base,postLittle,active,newPaths⟩,rank⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.PathInvariant.resolve_normal
