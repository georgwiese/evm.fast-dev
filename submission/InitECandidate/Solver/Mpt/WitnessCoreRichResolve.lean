import InitECandidate.Solver.Mpt.WitnessCoreRegistryFrame

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open Input.Main.RunAttemptConstructors

theorem ChildViews.pending (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : BitVec 64 → Prop)
    (entry : Entry) (rest : List Entry) (pending : BitVec 64) (children : ChildViews source valid (entry::rest)) :
    ChildViews source valid ({entry with pending:=some pending}::rest) := by
  intro current member
  rcases List.mem_cons.mp member with same|older
  · subst current; exact children entry List.mem_cons_self
  · exact children current (List.mem_cons_of_mem entry older)

theorem excludes_pending (memory : GasBudget.Memory) (domain : BitVec 64 → Prop) (graph : TrieWalk.Graph memory domain)
    (entry : Entry) (rest : List Entry) (pending : BitVec 64)
    (excludes : ∀ current∈entry::rest,∀ node index occupied,current.data.payload=.branch node index occupied → graph.Excludes node 176) :
    ∀ current∈{entry with pending:=some pending}::rest,∀ node index occupied,current.data.payload=.branch node index occupied → graph.Excludes node 176 := by
  intro current member node index occupied payload
  rcases List.mem_cons.mp member with same|older
  · subst current; exact excludes entry List.mem_cons_self node index occupied payload
  · exact excludes current (List.mem_cons_of_mem entry older) node index occupied payload

/-- A genuine original resolver iteration installs the actual pending
hash and either delivers a fresh result or supplies a bounded next input.
Both alternatives preserve the full invariant and decrease actual rank. -/
theorem RichInvariant.resolve_normal (input : Guest.InputBlob) (frontier : Nat) (db heap cursor limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stack : List Entry)
    (rich : RichInvariant input frontier db limit source ⟨heap,cursor,stack,.resolve,true⟩)
    (frontierLower : 2713731432≤frontier)
    (normal : evaluateHOLFiniteState source resolveBranch=(none,post)) :
    ∃ next : Configuration,RichInvariant input frontier db limit post next ∧
      next.rank limit<(Configuration.mk heap cursor stack .resolve true).rank limit := by
  have invariant:=rich.base
  obtain ⟨registry⟩:=rich.registry
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
  rcases shape with ⟨zero,node,result,mode,owned,resolved,rank⟩|⟨pointer,length,actualPointer,actualLength,mode,small,lower,before,validHash,rank⟩
  · have parentLower:=invariant.view.marks entry List.mem_cons_self
    have returnedOwned:=owned.weaken post node heap.toNat next.toNat (max frontier (resultLower (nextEntry::rest))) next.toNat
      (max_le invariant.frontierBefore parentLower) (Nat.le_refl _)
    obtain ⟨nodes,member,includes,members⟩:=registry.nodes.resolve_terminal source post frontier db heap next node
      above invariant.frontierBefore frame grows resolved nextCell scratch.domain invariant.aligned
    have childrenOld:=registry.children_database source post frontier db _ invariant.view nodes.graph includes frame
    have children : ChildViews post nodes.graph.valid (nextEntry::rest) := childrenOld.pending post nodes.graph.valid entry rest pending
    have freshResult : node≠0#64 → heap.toNat≤node.toNat := by intro active; exact (owned.resolve_left active).fresh
    have oldExcluded:=registry.excludes_extension source post frontier db _ invariant.view nodes.graph node members tags freshResult
    have excludes:=excludes_pending post.memory post.memaddrs nodes.graph entry rest pending oldExcluded
    have base : Invariant input frontier db limit post ⟨next,cursor,nextEntry::rest,.returning,true⟩ :=
      ⟨frozen,actualDb,nextCell,nextArena,aligned,invariant.heapLower.trans grows,invariant.frontierBefore.trans grows,
        scratch,invariant.below,view,fresh,words,top,mode,actualGo,⟨nextWaiting,node,result,returnedOwned⟩,Or.inl rfl,installed⟩
    have active : ActiveRegistry post frontier db ⟨next,cursor,nextEntry::rest,.returning,true⟩ := ⟨nodes,children,excludes,by
      intro phase child cell
      have same : child=node := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (cell.symm.trans result)))
      subst child
      exact member⟩
    exact ⟨⟨next,cursor,nextEntry::rest,.returning,true⟩,⟨base,⟨active⟩⟩,rank⟩
  · obtain ⟨oldNodes,validEq⟩:=registry.nodes.after_database_frame source post frontier heap db above frame
    let nodes:=oldNodes.advance_heap post frontier heap next db grows
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
    have active : ActiveRegistry post frontier db ⟨next,cursor,nextEntry::rest,.decode,true⟩ :=
      ⟨nodes,children,excludes,by intro phase; cases phase⟩
    exact ⟨⟨next,cursor,nextEntry::rest,.decode,true⟩,⟨base,⟨active⟩⟩,rank⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.RichInvariant.resolve_normal
