import InitECandidate.Solver.Mpt.WitnessCoreRegistryFrame
import InitECandidate.Solver.Mpt.WitnessCorePathRegistryPush
import InitECandidate.Solver.Mpt.WitnessCoreStackDecodeNibbles
import InitECandidate.Solver.Mpt.WitnessNodeRegistryDecodePaths

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open Input.Main.RunAttemptConstructors

/-- A genuine original decode iteration preserves the full closed-node
registry, initialized pending children and branch exclusions as well as
the actual physical/control invariant and strictly decreasing rank. -/
theorem PathInvariant.decode_normal (input : Guest.InputBlob) (frontier : Nat) (db heap cursor limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stack : List Entry)
    (model : PathInvariant input frontier db limit source ⟨heap,cursor,stack,.decode,true⟩)
    (frontierLower : 2713731432≤frontier)
    (normal : evaluateHOLFiniteState source decodeBranch=(none,post)) :
    ∃ next : Configuration,PathInvariant input frontier db limit post next ∧
      next.rank limit<(Configuration.mk heap cursor stack .decode true).rank limit := by
  have invariant:=model.base
  obtain ⟨registry,pathModel⟩:=model.registry
  obtain ⟨waiting,pointer,length,pointerCell,lengthCell,small,lower,before⟩:=invariant.phase
  obtain ⟨oldResult,resultCell⟩:=invariant.words.result
  obtain ⟨oldSlot,slotCell⟩:=invariant.words.slot
  obtain ⟨frame,step,dbCell,goCell,words⟩:=core_decode_stack_nibbles_normal input source post db pointer length heap cursor limit oldResult oldSlot 1#64 stack
    (invariant.boundary input frontier db limit source _) invariant.view invariant.dbCell pointerCell lengthCell invariant.topCell resultCell slotCell invariant.modeCell
    invariant.heapCell invariant.scratch invariant.heapLower before small lower invariant.below model.little invariant.installed normal
  have databaseFrame:=DatabaseFrame.of_decode source post heap cursor limit frame invariant.below
  have frozen:=invariant.frozen.database_frame input source post frontier heap invariant.frontierBefore databaseFrame dbCell
  have actualDb:=dbCell.trans invariant.dbCell
  have actualGo:=goCell.trans invariant.goCell
  have installed : Input.OriginalCode.Installed post.code:=by rw [frame.code]; exact invariant.installed
  have above : cursor.toNat≤frontier := by have below : cursor.toNat≤2713717616 := invariant.below; omega
  have tags:=registry.nodes.tags_normal source post frontier heap db cursor limit above frame
  have postLittle : post.be=false:=frame.endian.trans model.little
  obtain ⟨oldNodes,validEq⟩:=registry.nodes.after_normal_frame source post frontier heap heap db cursor limit above (Nat.le_refl _) frame
  have oldIncludes : ∀ node,registry.nodes.graph.valid node → oldNodes.graph.valid node:=by
    intro node member; rw [validEq]; exact member
  have oldChildren:=registry.children.normal_frame source post registry.nodes.graph.valid oldNodes.graph.valid db heap cursor limit stack
    invariant.view oldIncludes invariant.below frame
  have oldExcludes:=registry.excludes_same source post frontier db _ oldNodes.graph validEq tags
  let oldRegistry : ActiveRegistry post frontier db ⟨heap,cursor,stack,.decode,true⟩:=
    ⟨oldNodes,oldChildren,oldExcludes,(by intro phase; cases phase)⟩
  have oldPaths : oldRegistry.PathModel:=pathModel.normal_frame source post frontier db limit _ registry oldRegistry validEq invariant.view invariant.below frontierLower frame
  have oldView:=invariant.view.frame source post db cursor.toNat heap.toNat cursor.toNat heap.toNat stack invariant.heapLower
    (Nat.le_refl _) (Nat.le_refl _) frame.domain frame.memory
  have oldBounded (current : Entry) (member : current∈stack) : current.data.BeforeHeap heap.toNat:=
    (oldView.before current member).mono current.data current.mark heap.toNat (oldView.marks current member)
  cases step with
  | terminal next node nextCell nextArena aligned grows scratch view top result mode owned decoded rank=>
    have parentLower:=invariant.view.result_lower_le_heap source db cursor.toNat heap.toNat stack invariant.heapLower
    have returnedOwned:=owned.weaken post node heap.toNat next.toNat (max frontier (resultLower stack)) next.toNat
      (max_le invariant.frontierBefore parentLower) (Nat.le_refl _)
    obtain ⟨decodedPointer,decodedLength,decodedResult⟩:=decoded
    obtain ⟨nodes,nodesPaths,member,includes,members⟩:=registry.nodes.decode_terminal_paths source post frontier db decodedPointer decodedLength heap next cursor limit node
      pathModel.nodes (by have below : cursor.toNat≤2713717616:=invariant.below; omega) invariant.frontierBefore frame decodedResult nextCell
    have children:=registry.children.normal_frame source post registry.nodes.graph.valid nodes.graph.valid db heap cursor limit stack
      invariant.view includes invariant.below frame
    have freshResult : node≠0#64 → heap.toNat≤node.toNat := by
      intro active
      exact (owned.resolve_left active).fresh
    have excludes:=registry.excludes_extension source post frontier db _ invariant.view nodes.graph node members tags freshResult
    have base : Invariant input frontier db limit post ⟨next,cursor,stack,.returning,true⟩ :=
      ⟨frozen,actualDb,nextCell,nextArena,aligned,invariant.heapLower.trans grows,invariant.frontierBefore.trans grows,
        scratch,invariant.below,view,invariant.fresh,words,top,mode,actualGo,⟨waiting,node,result,returnedOwned⟩,Or.inl rfl,installed⟩
    let active : ActiveRegistry post frontier db ⟨next,cursor,stack,.returning,true⟩ := ⟨nodes,children,excludes,by
      intro phase child cell
      have same : child=node := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (cell.symm.trans result)))
      subst child
      exact member⟩
    have allocation (nonnull : node≠0#64) : AllocatedBytes.Arena node (TrieWalk.nodeBytes (GasBudget.wordAt post.memory node)):=by
      cases decodedResult with
      | empty scratch=>exact (nonnull rfl).elim
      | leaf node nibbles nibbleLength valuePointer valueLength finalHeap view freshPath freshNode scratch heapCell heapArena heapAligned nodeBefore pathBytes pathAligned pathBefore=>
        have tag : GasBudget.wordAt post.memory node=1#64:=by simp [GasBudget.wordAt,view.tag,MemoryBytes.wordBits]
        simpa [tag,TrieWalk.nodeBytes] using view.arena
    have newPath (nonnull : node≠0#64) (tag : GasBudget.wordAt post.memory node=1#64 ∨ GasBudget.wordAt post.memory node=2#64) :
        heap.toNat≤(GasBudget.wordAt post.memory (node+32#64)).toNat ∧ (GasBudget.wordAt post.memory (node+32#64)).toNat%8=0:=by
      cases decodedResult with
      | empty scratch=>exact (nonnull rfl).elim
      | leaf node nibbles nibbleLength valuePointer valueLength finalHeap view freshPath freshNode scratch heapCell heapArena heapAligned nodeBefore pathBytes pathAligned pathBefore=>
        have pointerCell : GasBudget.wordAt post.memory (node+32#64)=nibbles:=by
          simp [GasBudget.wordAt,view.cells (32,nibbles) (by simp),MemoryBytes.wordBits]
        rw [pointerCell]
        exact ⟨freshPath,pathAligned⟩
    have currentMembers : ∀ owner,nodes.graph.valid owner → oldRegistry.nodes.graph.valid owner ∨ owner=node:=by
      intro owner current
      rcases members owner current with prior|same
      · left; change oldNodes.graph.valid owner; rw [validEq]; exact prior
      · exact Or.inr same
    have newPaths : active.PathModel:=oldPaths.node_added post frontier db _ _ node oldRegistry active nodesPaths rfl oldView.records oldBounded currentMembers freshResult allocation newPath
    exact ⟨⟨next,cursor,stack,.returning,true⟩,⟨base,postLittle,active,newPaths⟩,rank⟩
  | pushed data next nextCell nextArena aligned grows scratch view fresh initial freshRows freshPayload pathBytes top slot mode rank=>
    let entry : Entry:=⟨WitnessRecord.pointer cursor,data,next.toNat,none⟩
    have freshStack : FreshFrom frontier (entry::stack):=
      invariant.fresh.cons frontier entry stack (invariant.frontierBefore.trans freshRows) (invariant.frontierBefore.trans freshPayload)
    have below : (WitnessRecord.pointer cursor).toNat≤2713717616:=by
      have ceiling:=(view.records entry List.mem_cons_self).ceiling
      change (WitnessRecord.pointer cursor).toNat+88≤2713717616 at ceiling
      omega
    let nodes:=oldNodes.advance_heap post frontier heap next db grows
    have includes : ∀ node,registry.nodes.graph.valid node → nodes.graph.valid node := by
      intro node member
      change oldNodes.graph.valid node
      rw [validEq]
      exact member
    have childrenOld:=registry.children.normal_frame source post registry.nodes.graph.valid nodes.graph.valid db heap cursor limit stack
      invariant.view includes invariant.below frame
    have children : ChildViews post nodes.graph.valid (entry::stack) :=
      ChildViews.cons post nodes.graph.valid entry stack (ChildView.fresh post nodes.graph.valid entry fresh initial) childrenOld
    have excludedOld:=registry.excludes_same source post frontier db _ nodes.graph validEq tags
    have excludes : ∀ current∈entry::stack,∀ node index occupied,current.data.payload=.branch node index occupied → nodes.graph.Excludes node 176 := by
      intro current member node index occupied payload
      rcases List.mem_cons.mp member with same|older
      · subst current
        have after : heap.toNat≤node.toNat := by
          have lower : heap.toNat≤entry.data.payload.startAddress := freshPayload
          simpa only [payload,WitnessRecord.Payload.startAddress] using lower
        exact oldNodes.excludes_fresh post frontier heap db node 176 after
      · exact excludedOld current older node index occupied payload
    have base : Invariant input frontier db limit post ⟨next,WitnessRecord.pointer cursor,entry::stack,.resolve,true⟩ :=
      ⟨frozen,actualDb,nextCell,nextArena,aligned,invariant.heapLower.trans grows,invariant.frontierBefore.trans grows,
        scratch,below,view,freshStack,words,top,mode,actualGo,⟨entry,stack,rfl,waiting,slot⟩,Or.inl rfl,installed⟩
    let active : ActiveRegistry post frontier db ⟨next,WitnessRecord.pointer cursor,entry::stack,.resolve,true⟩ :=
      ⟨nodes,children,excludes,by intro phase; cases phase⟩
    have nodesPaths : nodes.PathModel:=oldPaths.nodes.advance_heap post frontier heap next db oldNodes grows
    have newPaths : active.PathModel:=oldPaths.record_added post frontier db _ _ entry oldRegistry active nodesPaths rfl rfl oldView.records oldBounded
      (view.records entry List.mem_cons_self) pathBytes freshPayload
    exact ⟨⟨next,WitnessRecord.pointer cursor,entry::stack,.resolve,true⟩,⟨base,postLittle,active,newPaths⟩,rank⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.PathInvariant.decode_normal
