import InitECandidate.Solver.Mpt.WitnessCoreRegistryBranchAdvance
import InitECandidate.Solver.Mpt.WitnessCoreRegistryFrame

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- The actual continuing-child state gains precisely the completed
current slot, retains every older pending branch and completed node, and
returns to resolve with its original physical branch allocation excluded. -/
theorem ActiveRegistry.branch_advanced (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap cursor node child : BitVec 64) (entry : Entry) (rest : List Entry)
    (index nextIndex : Fin 16) (occupied : Fin 17) (used : occupied.val≤index.val) (nextIndexEq : nextIndex.val=index.val+1)
    (registry : ActiveRegistry source frontier db ⟨heap,cursor,entry::rest,.returning,true⟩)
    (view : View source db cursor.toNat heap.toNat (entry::rest)) (payload : entry.data.payload=.branch node index occupied)
    (frontierLower : 2713731432≤frontier) (childMember : registry.nodes.graph.valid child) :
    let nextOccupied:=occupiedNext index occupied used child
    let nextEntry : Entry:={entry with data:={entry.data with payload:=.branch node nextIndex nextOccupied}}
    let post:=advanced (branchCounterEntry source entry.record node child index occupied) entry.record nextIndex
    Nonempty (ActiveRegistry post frontier db ⟨heap,cursor,nextEntry::rest,.resolve,true⟩) := by
  let middle:=branchCounterEntry source entry.record node child index occupied
  let post:=advanced middle entry.record nextIndex
  let nextOccupied:=occupiedNext index occupied used child
  let nextEntry : Entry:={entry with data:={entry.data with payload:=.branch node nextIndex nextOccupied}}
  have head:=view.records entry List.mem_cons_self
  have owned:=head.owned
  simp only [payload,WitnessRecord.Payload.Owned] at owned
  have floor : 2713731432≤node.toNat := by simpa only [payload,WitnessRecord.Payload.startAddress] using head.payloadFloor
  have ceiling:=head.ceiling
  have excluded:=registry.excludes entry List.mem_cons_self node index occupied payload
  obtain ⟨nodes,validEq⟩:=registry.nodes.branch_advanced source frontier db heap entry.record node child index nextIndex occupied frontierLower excluded owned.1 ceiling
  have includes : ∀ pointer,registry.nodes.graph.valid pointer → nodes.graph.valid pointer := by intro pointer member; rw [validEq]; exact member
  have headChildren:=registry.children entry List.mem_cons_self
  simp only [ChildView,payload] at headChildren
  have counterChildren:=headChildren.1.counter_entry source registry.nodes.graph.valid entry.record node child index occupied childMember owned.1 floor ceiling
  have nextChildren:=counterChildren.advanced middle registry.nodes.graph.valid entry.record node nextIndex (index.val+1) (by have bound:=index.isLt; omega) owned.1 floor ceiling
  have headPrefix : Children post nodes.graph.valid node nextIndex.val := by
    rw [nextIndexEq]
    exact nextChildren.enlarge post registry.nodes.graph.valid nodes.graph.valid node (index.val+1) includes
  have counterEmpty:=headChildren.2.counter_entry source entry.record node child index occupied owned.1 floor ceiling
  have headEmpty:=counterEmpty.advanced middle entry.record node nextIndex owned.1 floor ceiling
  have tailView:=view.tail source db cursor.toNat heap.toNat entry rest
  have tailChildren : ChildViews post nodes.graph.valid rest := by
    apply (registry.children.tail source registry.nodes.graph.valid entry rest).frame source post registry.nodes.graph.valid nodes.graph.valid db cursor.toNat heap.toNat rest tailView includes
    intro parent member query lower upper
    have parentFloor:=(view.records parent (List.mem_cons_of_mem entry member)).payloadFloor
    have before : parent.mark≤node.toNat := by
      have bound:=(view.ordered.1 parent member).2.2
      simpa only [payload,WitnessRecord.Payload.startAddress] using bound
    exact (advanced_above_memory middle entry.record nextIndex ceiling query (by omega)).trans
      (branch_counter_outside_memory source entry.record node child index occupied owned.1 ceiling query (by omega) (Or.inl (by omega)))
  have children : ChildViews post nodes.graph.valid (nextEntry::rest) := ChildViews.cons post nodes.graph.valid nextEntry rest ⟨headPrefix,headEmpty⟩ tailChildren
  have counterTags:=registry.nodes.branch_counter_tags source frontier db heap entry.record node child index occupied frontierLower excluded owned.1 ceiling
  have tags : ∀ pointer,registry.nodes.graph.valid pointer → pointer≠0#64 → wordAt post.memory pointer=wordAt source.memory pointer := by
    intro pointer member active
    have lower:=(registry.nodes.regions pointer member active).1
    calc
      wordAt post.memory pointer=wordAt middle.memory pointer := by
        unfold wordAt
        rw [advanced_above_memory middle entry.record nextIndex ceiling pointer (by omega)]
      _=wordAt source.memory pointer := counterTags pointer member active
  have allExcluded:=registry.excludes_same source post frontier db _ nodes.graph validEq tags
  have nextExcluded : ∀ current∈nextEntry::rest,∀ pointer i occ,current.data.payload=.branch pointer i occ → nodes.graph.Excludes pointer 176 := by
    intro current member pointer i occ currentPayload
    rcases List.mem_cons.mp member with same|older
    · subst current
      change WitnessRecord.Payload.branch node nextIndex nextOccupied=WitnessRecord.Payload.branch pointer i occ at currentPayload
      cases currentPayload
      exact allExcluded entry List.mem_cons_self node index occupied payload
    · exact allExcluded current (List.mem_cons_of_mem entry older) pointer i occ currentPayload
  exact ⟨⟨nodes,children,nextExcluded,by intro phase; cases phase⟩⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.branch_advanced
