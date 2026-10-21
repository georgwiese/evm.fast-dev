import InitECandidate.Solver.Mpt.WitnessCoreRegistryFrame

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open Input.Main.RunAttemptConstructors

/-- A genuine original decode iteration preserves the full closed-node
registry, initialized pending children and branch exclusions as well as
the actual physical/control invariant and strictly decreasing rank. -/
theorem RichInvariant.decode_normal (input : Guest.InputBlob) (frontier : Nat) (db heap cursor limit : BitVec 64)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stack : List Entry)
    (rich : RichInvariant input frontier db limit source ⟨heap,cursor,stack,.decode,true⟩)
    (frontierLower : 2713731432≤frontier)
    (normal : evaluateHOLFiniteState source decodeBranch=(none,post)) :
    ∃ next : Configuration,RichInvariant input frontier db limit post next ∧
      next.rank limit<(Configuration.mk heap cursor stack .decode true).rank limit := by
  have invariant:=rich.base
  obtain ⟨registry⟩:=rich.registry
  obtain ⟨waiting,pointer,length,pointerCell,lengthCell,small,lower,before⟩:=invariant.phase
  obtain ⟨oldResult,resultCell⟩:=invariant.words.result
  obtain ⟨oldSlot,slotCell⟩:=invariant.words.slot
  obtain ⟨frame,step,dbCell,goCell,words⟩:=core_decode_stack_normal input source post db pointer length heap cursor limit oldResult oldSlot 1#64 stack
    (invariant.boundary input frontier db limit source _) invariant.view invariant.dbCell pointerCell lengthCell invariant.topCell resultCell slotCell invariant.modeCell
    invariant.heapCell invariant.scratch invariant.heapLower before small lower invariant.below invariant.installed normal
  have databaseFrame:=DatabaseFrame.of_decode source post heap cursor limit frame invariant.below
  have frozen:=invariant.frozen.database_frame input source post frontier heap invariant.frontierBefore databaseFrame dbCell
  have actualDb:=dbCell.trans invariant.dbCell
  have actualGo:=goCell.trans invariant.goCell
  have installed : Input.OriginalCode.Installed post.code:=by rw [frame.code]; exact invariant.installed
  have above : cursor.toNat≤frontier := by have below : cursor.toNat≤2713717616 := invariant.below; omega
  have tags:=registry.nodes.tags_normal source post frontier heap db cursor limit above frame
  cases step with
  | terminal next node nextCell nextArena aligned grows scratch view top result mode owned decoded rank=>
    have parentLower:=invariant.view.result_lower_le_heap source db cursor.toNat heap.toNat stack invariant.heapLower
    have returnedOwned:=owned.weaken post node heap.toNat next.toNat (max frontier (resultLower stack)) next.toNat
      (max_le invariant.frontierBefore parentLower) (Nat.le_refl _)
    obtain ⟨decodedPointer,decodedLength,decodedResult⟩:=decoded
    obtain ⟨nodes,member,includes,members⟩:=registry.nodes.decode_terminal source post frontier db decodedPointer decodedLength heap next cursor limit node
      above invariant.frontierBefore frame decodedResult nextCell
    have children:=registry.children.normal_frame source post registry.nodes.graph.valid nodes.graph.valid db heap cursor limit stack
      invariant.view includes invariant.below frame
    have freshResult : node≠0#64 → heap.toNat≤node.toNat := by
      intro active
      exact (owned.resolve_left active).fresh
    have excludes:=registry.excludes_extension source post frontier db _ invariant.view nodes.graph node members tags freshResult
    have base : Invariant input frontier db limit post ⟨next,cursor,stack,.returning,true⟩ :=
      ⟨frozen,actualDb,nextCell,nextArena,aligned,invariant.heapLower.trans grows,invariant.frontierBefore.trans grows,
        scratch,invariant.below,view,invariant.fresh,words,top,mode,actualGo,⟨waiting,node,result,returnedOwned⟩,Or.inl rfl,installed⟩
    have active : ActiveRegistry post frontier db ⟨next,cursor,stack,.returning,true⟩ := ⟨nodes,children,excludes,by
      intro phase child cell
      have same : child=node := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (cell.symm.trans result)))
      subst child
      exact member⟩
    exact ⟨⟨next,cursor,stack,.returning,true⟩,⟨base,⟨active⟩⟩,rank⟩
  | pushed data next nextCell nextArena aligned grows scratch view fresh initial freshRows freshPayload top slot mode rank=>
    let entry : Entry:=⟨WitnessRecord.pointer cursor,data,next.toNat,none⟩
    have freshStack : FreshFrom frontier (entry::stack):=
      invariant.fresh.cons frontier entry stack (invariant.frontierBefore.trans freshRows) (invariant.frontierBefore.trans freshPayload)
    have below : (WitnessRecord.pointer cursor).toNat≤2713717616:=by
      have ceiling:=(view.records entry List.mem_cons_self).ceiling
      change (WitnessRecord.pointer cursor).toNat+88≤2713717616 at ceiling
      omega
    obtain ⟨oldNodes,validEq⟩:=registry.nodes.after_normal_frame source post frontier heap heap db cursor limit above (Nat.le_refl _) frame
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
    have active : ActiveRegistry post frontier db ⟨next,WitnessRecord.pointer cursor,entry::stack,.resolve,true⟩ :=
      ⟨nodes,children,excludes,by intro phase; cases phase⟩
    exact ⟨⟨next,WitnessRecord.pointer cursor,entry::stack,.resolve,true⟩,⟨base,⟨active⟩⟩,rank⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.RichInvariant.decode_normal
