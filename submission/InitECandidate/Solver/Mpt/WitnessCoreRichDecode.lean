import InitECandidate.Solver.Mpt.WitnessCoreRegistryFrame

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open Input.Main.RunAttemptConstructors

/-- A genuine original decode iteration preserves the full closed-node
registry, initialized pending children and branch exclusions as well as
the actual physical/control invariant and strictly decreasing rank. -/
theorem RichInvariant.decode_normal (input : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db heap cursor limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stack : List Entry)
    (rich : RichInvariant input frontier db limit source ⟨heap,cursor,stack,.decode,true⟩)
    (normal : evaluateHOLFiniteState source decodeBranch=(none,post)) :
    ∃ next : Configuration,RichInvariant input frontier db limit post next ∧
      next.rank limit<(Configuration.mk heap cursor stack .decode true).rank limit := by
  have invariant:=rich.base
  obtain ⟨registry⟩:=rich.registry
  obtain ⟨waiting,pointer,length,pointerCell,lengthCell,small,lower,before⟩:=invariant.phase
  obtain ⟨oldResult,resultCell⟩:=invariant.words.result
  obtain ⟨oldSlot,slotCell⟩:=invariant.words.slot
  obtain ⟨frame,step,dbCell,goCell,words⟩:=core_decode_stack_normal source post db pointer length heap cursor limit oldResult oldSlot 1#64 stack
    invariant.view invariant.dbCell pointerCell lengthCell invariant.topCell resultCell slotCell invariant.modeCell
    invariant.heapCell invariant.heapArena invariant.heapBound invariant.aligned invariant.live invariant.scratch
    (invariant.db_before input frontier db limit source _) before small lower normal
  have database:=invariant.database.of_before heap.toNat (invariant.tableBefore.trans invariant.frontierBefore) frame.domain frame.endian frame.memoryBefore
  have actualDb:=dbCell.trans invariant.dbCell
  have actualGo:=goCell.trans invariant.goCell
  have installed : Input.OriginalCode.Installed post.code:=by rw [frame.code]; exact invariant.installed
  have tags:=registry.nodes.tags_normal source post frontier heap db cursor limit frame
  cases step with
  | terminal next node nextCell nextArena nextBound aligned grows scratch nextLive view top result mode owned decoded rank=>
    have parentLower:=invariant.view.result_lower_le_heap source db cursor.toNat heap.toNat stack invariant.heapLower
    have returnedOwned:=owned.weaken post node heap.toNat next.toNat (max frontier (resultLower stack)) next.toNat
      (max_le invariant.frontierBefore parentLower) (Nat.le_refl _)
    obtain ⟨decodedPointer,decodedLength,decodedResult⟩:=decoded
    obtain ⟨nodes,member,includes,members⟩:=registry.nodes.decode_terminal source post frontier db decodedPointer decodedLength heap next cursor limit node
      invariant.frontierBefore frame decodedResult nextCell
    have children:=registry.children.live_frame source post registry.nodes.graph.valid nodes.graph.valid db heap cursor limit stack
      invariant.view includes frame
    have freshResult : node≠0#64 → heap.toNat≤node.toNat := by
      intro active
      exact (owned.resolve_left active).fresh
    have excludes:=registry.excludes_extension source post frontier db _ invariant.view nodes.graph node members tags freshResult
    have base : Invariant input frontier db limit post ⟨next,cursor,stack,.returning,true⟩ :=
      ⟨database,invariant.tableBefore,invariant.databaseEq,actualDb,nextCell,nextArena,nextBound,aligned,invariant.heapLower.trans grows,invariant.frontierBefore.trans grows,
        scratch,nextLive,view,invariant.fresh,words,top,mode,actualGo,⟨waiting,node,result,returnedOwned⟩,Or.inl rfl,installed⟩
    have active : ActiveRegistry post frontier db ⟨next,cursor,stack,.returning,true⟩ := ⟨nodes,children,excludes,by
      intro phase child cell
      have same : child=node := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (cell.symm.trans result)))
      subst child
      exact member⟩
    exact ⟨⟨next,cursor,stack,.returning,true⟩,⟨base,⟨active⟩⟩,rank⟩
  | pushed data next nextCell nextArena nextBound aligned grows scratch nextLive view fresh initial freshRows freshPayload top slot mode rank=>
    let entry : Entry:=⟨WitnessRecord.pointer cursor,data,next.toNat,none⟩
    have freshStack : FreshFrom frontier (entry::stack):=
      invariant.fresh.cons frontier entry stack (invariant.frontierBefore.trans freshRows) (invariant.frontierBefore.trans freshPayload)
    obtain ⟨oldNodes,validEq⟩:=registry.nodes.after_live_frame source post frontier heap heap db cursor limit (Nat.le_refl _) frame
    let nodes:=oldNodes.advance_heap post frontier heap next db grows
    have includes : ∀ node,registry.nodes.graph.valid node → nodes.graph.valid node := by
      intro node member
      change oldNodes.graph.valid node
      rw [validEq]
      exact member
    have childrenOld:=registry.children.live_frame source post registry.nodes.graph.valid nodes.graph.valid db heap cursor limit stack
      invariant.view includes frame
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
      ⟨database,invariant.tableBefore,invariant.databaseEq,actualDb,nextCell,nextArena,nextBound,aligned,invariant.heapLower.trans grows,invariant.frontierBefore.trans grows,
        scratch,nextLive,view,freshStack,words,top,mode,actualGo,⟨entry,stack,rfl,waiting,slot⟩,Or.inl rfl,installed⟩
    have active : ActiveRegistry post frontier db ⟨next,WitnessRecord.pointer cursor,entry::stack,.resolve,true⟩ :=
      ⟨nodes,children,excludes,by intro phase; cases phase⟩
    exact ⟨⟨next,WitnessRecord.pointer cursor,entry::stack,.resolve,true⟩,⟨base,⟨active⟩⟩,rank⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.RichInvariant.decode_normal
