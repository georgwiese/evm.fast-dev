import InitECandidate.Solver.Mpt.WitnessCoreRegistryBranchFinish
import InitECandidate.Solver.Mpt.WitnessCoreRegistryBranchAdvance
import InitECandidate.Solver.Mpt.WitnessCoreRegistryTailFrame

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The genuine original last-child path completes all sixteen physical
slots, parses the real final value, registers the completed branch and
pops its actual parent while retaining every older pending branch. -/
theorem ActiveRegistry.branch_last_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap cursor limit node child : BitVec 64) (entry : Entry) (rest : List Entry)
    (index : Fin 16) (occupied : Fin 17) (used : occupied.val≤index.val) (last : ¬index.val+1<16)
    (registry : ActiveRegistry source frontier db ⟨heap,cursor,entry::rest,.returning,true⟩)
    (view : View source db cursor.toNat heap.toNat (entry::rest)) (payload : entry.data.payload=.branch node index occupied)
    (frontierLower : 2713731432≤frontier) (nodeFloor : frontier≤node.toNat) (dbUpper : db.toNat≤33806089496)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word entry.record)))
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word node)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index.val))))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source branchChildren=(none,post)) :
    Nonempty (ActiveRegistry post frontier db ⟨heap,cursor,rest,.returning,true⟩) := by
  have head:=view.records entry List.mem_cons_self
  have before:=(view.before entry List.mem_cons_self).mono entry.data entry.mark heap.toNat (view.marks entry List.mem_cons_self)
  have aboveRecord:=view.above entry List.mem_cons_self
  have heapLower : 2713731432≤heap.toNat := by have lower:=head.arrayFloor; have upper:=before.1; omega
  have below : cursor.toNat≤2713717616 := by have ceiling:=head.ceiling; omega
  have owned:=head.owned
  simp only [payload,WitnessRecord.Payload.Owned] at owned
  have nodeBefore : node.toNat+176≤heap.toNat := by simpa only [payload,WitnessRecord.Payload.endAddress] using before.2
  obtain ⟨tail,returnedOwned,actualTop,actualResult,globals,scratch,locals,band,domain,endian,code,rank⟩:=branch_children_last_stack_normal source post
    db heap cursor limit node child entry rest index occupied used last view payload topCell branchCell indexCell resultCell arena installed normal
  let middle:=branchCounterEntry source entry.record node child index occupied
  let nextOccupied:=occupiedNext index occupied used child
  let currentData:=(WitnessRecord.BranchCounter.occupied nextOccupied).description entry.data node index occupied
  obtain ⟨item,built,header,bytes,flag,selected,valid,enough,upper,postArena,postGlobals,postDomain,postEndian,postCode,postEq,above⟩:=
    branch_children_last_normal source post entry.record db node (top rest) child heap cursor limit entry.data index occupied used last head payload
      topCell branchCell indexCell resultCell view.links.1 arena before aboveRecord below heapLower installed normal
  have frontierNode : 2713731432≤node.toNat := frontierLower.trans nodeFloor
  have excluded:=registry.excludes entry List.mem_cons_self node index occupied payload
  obtain ⟨middleNodes,middleValid⟩:=registry.nodes.branch_counter source frontier db heap entry.record node child index occupied frontierLower excluded owned.1 head.ceiling
  have middleIncludes : ∀ pointer,registry.nodes.graph.valid pointer → middleNodes.graph.valid pointer := by intro pointer member; rw [middleValid]; exact member
  have counterTags:=registry.nodes.branch_counter_tags source frontier db heap entry.record node child index occupied frontierLower excluded owned.1 head.ceiling
  have middleExcluded:=excluded.of_agreement source.memory middle.memory source.memaddrs middle.memaddrs registry.nodes.graph middleNodes.graph node 176 middleValid counterTags
  have currentChildren:=registry.children entry List.mem_cons_self
  simp only [ChildView,payload] at currentChildren
  have childMember:=registry.returned rfl child resultCell
  have counterChildren:=currentChildren.1.counter_entry source registry.nodes.graph.valid entry.record node child index occupied childMember owned.1 frontierNode head.ceiling
  have complete : index.val+1=16 := by have bound:=index.isLt; omega
  have allChildren : Children middle middleNodes.graph.valid node 16 := by
    rw [←complete]
    exact counterChildren.enlarge middle registry.nodes.graph.valid middleNodes.graph.valid node (index.val+1) middleIncludes
  have empty:=currentChildren.2.counter_entry source entry.record node child index occupied owned.1 frontierNode head.ceiling
  have currentView:=branch_counter_entry_view source entry.record db node child entry.data index occupied used head payload
  have currentPayload : currentData.payload=.branch node index nextOccupied := rfl
  have middleDomain : middle.memaddrs=source.memaddrs := by unfold middle branchCounterEntry occupancyState; split <;> rfl
  have postBuilt : post.memaddrs=built.memaddrs := by
    rw [postEq]
    unfold branchFinishedState branchValueState
    split
    · split <;> rfl
    · rfl
  have builtDomain : built.memaddrs=middle.memaddrs := postBuilt.symm.trans (postDomain.trans middleDomain.symm)
  have registered : ∃ nodes : NodeRegistry post frontier heap db,nodes.graph.valid node ∧
      (∀ pointer,middleNodes.graph.valid pointer → nodes.graph.valid pointer) ∧
      (∀ pointer,nodes.graph.valid pointer → middleNodes.graph.valid pointer ∨ pointer=node) := by
    rw [postEq]
    exact middleNodes.branch_finished middle built frontier entry.record db heap node (top rest) cursor header bytes flag currentData index nextOccupied item
      frontierLower currentView currentPayload allChildren empty selected dbUpper valid below above builtDomain nodeFloor nodeBefore middleExcluded
  obtain ⟨nodes,nodeMember,forward,backward⟩:=registered
  have includes : ∀ pointer,registry.nodes.graph.valid pointer → nodes.graph.valid pointer := fun pointer member=>forward pointer (middleIncludes pointer member)
  have members : ∀ pointer,nodes.graph.valid pointer → registry.nodes.graph.valid pointer ∨ pointer=node := by
    intro pointer member
    rcases backward pointer member with prior|fresh
    · left; rw [←middleValid]; exact prior
    · exact Or.inr fresh
  have tags : ∀ pointer,registry.nodes.graph.valid pointer → pointer≠0#64 → wordAt post.memory pointer=wordAt source.memory pointer := by
    intro pointer member active
    have required : registry.nodes.graph.Footprint pointer := .header pointer member active
    have bounds:=registry.nodes.graph.footprint_bounds frontier heap.toNat registry.nodes.regions pointer required
    have outside:=registry.nodes.graph.excluded_footprint frontier heap.toNat registry.nodes.regions node 176 excluded pointer required
    calc
      wordAt post.memory pointer=wordAt middle.memory pointer := by
        unfold wordAt
        rw [postEq,branch_finished_outside_memory middle built node (top rest) cursor header bytes flag currentData nextOccupied owned.1 below above pointer (frontierLower.trans bounds.1) outside]
      _=wordAt source.memory pointer := counterTags pointer member active
  have tailChildren:=registry.children.return_tail source post registry.nodes.graph.valid nodes.graph.valid db cursor.toNat heap.toNat entry rest view includes band
  have tailExcluded:=registry.tail_excludes_extension source post frontier db heap cursor entry rest view nodes.graph node members tags
    (by intro active; simp only [payload,WitnessRecord.Payload.startAddress]; exact Nat.le_refl _)
  refine ⟨⟨nodes,tailChildren,tailExcluded,?_⟩⟩
  intro phase pointer cell
  have same : pointer=node := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (cell.symm.trans actualResult)))
  subst pointer
  exact nodeMember

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.branch_last_normal
