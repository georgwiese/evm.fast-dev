import InitECandidate.Solver.Mpt.WitnessCoreRegistryBranchPrefix
import InitECandidate.Solver.Mpt.TrieGraphExclusion

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- The real parser's scratch writes and the actual final branch stores
preserve every persistent word outside the pending branch allocation. -/
theorem branch_finished_outside_memory (source built : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node previous cursor header bytes flag : BitVec 64) (data : WitnessRecord.Description) (occupied : Fin 17)
    (arena : AllocatedBytes.Arena node 176) (below : cursor.toNat≤2713717616)
    (above : Rlp.Validation.Above source built cursor.toNat) (query : BitVec 64) (floor : 2713731432≤query.toNat)
    (outside : query.toNat<node.toNat ∨ node.toNat+176≤query.toNat) :
    (branchFinishedState source built node previous data header bytes flag occupied).memory query=source.memory query := by
  have away (offset : Nat) (inside : offset<176) : query≠node+BitVec.ofNat 64 offset := by
    have number : (node+BitVec.ofNat 64 offset).toNat=node.toNat+offset := byteAddress_toNat node offset (by have upper:=arena.upper; omega)
    intro equal
    have numeric:=congrArg BitVec.toNat equal
    rw [number] at numeric
    omega
  exact (branch_finished_field_memory source built node previous data header bytes flag occupied query
    (away 8 (by decide)) (away 16 (by decide)) (away 160 (by decide)) (away 168 (by decide))).trans (above query (by omega))

/-- Register the real completed branch from its sixteen returned slots,
actual RLP value result and exact final state. The genuine parser may
change scratch; every older completed node is framed by its exclusion. -/
theorem NodeRegistry.branch_finished (source built : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (record db heap node previous cursor header bytes flag : BitVec 64)
    (data : WitnessRecord.Description) (index : Fin 16) (occupied : Fin 17) (item : Rlp.ListItem)
    (registry : NodeRegistry source frontier heap db) (frontierLower : 2713731432≤frontier)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied)
    (children : Children source registry.graph.valid node 16) (empty : EmptyValue source node)
    (selected : data.items[16]?=some item) (dbUpper : db.toNat≤33806089496)
    (valid : Rlp.Item.Valid (Rlp.Slices.itemPointer data.listPointer data.items 16) item.total.toNat
      (Rlp.Item.result (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag))
    (below : cursor.toNat≤2713717616) (above : Rlp.Validation.Above source built cursor.toNat) (builtDomain : built.memaddrs=source.memaddrs)
    (floor : frontier≤node.toNat) (before : node.toNat+176≤heap.toNat) (excluded : registry.graph.Excludes node 176) :
    let post:=branchFinishedState source built node previous data header bytes flag occupied
    ∃ next : NodeRegistry post frontier heap db,next.graph.valid node ∧
      (∀ pointer,registry.graph.valid pointer → next.graph.valid pointer) ∧
      (∀ pointer,next.graph.valid pointer → registry.graph.valid pointer ∨ pointer=node) := by
  let post:=branchFinishedState source built node previous data header bytes flag occupied
  have owned:=view.owned
  simp only [payload,WitnessRecord.Payload.Owned] at owned
  have domain : post.memaddrs=source.memaddrs := by
    unfold post branchFinishedState branchValueState
    split
    · split <;> exact builtDomain
    · exact builtDomain
  have agree : ∀ query,registry.graph.Footprint query → post.memory query=source.memory query := by
    intro query required
    have bounds:=registry.graph.footprint_bounds frontier heap.toNat registry.regions query required
    have outside:=registry.graph.excluded_footprint frontier heap.toNat registry.regions node 176 excluded query required
    exact branch_finished_outside_memory source built node previous cursor header bytes flag data occupied owned.1 below above query (frontierLower.trans bounds.1) outside
  have valueAgree : ∀ query,TrieWalk.ValueFootprint registry.graph query → post.memory query=source.memory query := by
    intro query required
    have bounds:=registry.graph.value_bounds frontier heap.toNat registry.regions query required
    have outside:=registry.graph.excluded_value frontier heap.toNat registry.regions node 176 excluded query required
    exact branch_finished_outside_memory source built node previous cursor header bytes flag data occupied owned.1 below above query (frontierLower.trans bounds.1) outside
  obtain ⟨graph,validEq,regions,disjoint,⟨values⟩⟩:=registry.graph.after_agreement source post 1024 frontier heap.toNat (WitnessValue db)
    registry.values registry.regions registry.disjoint domain agree valueAgree
  let current : NodeRegistry post frontier heap db:=⟨graph,values,regions,disjoint⟩
  have includes : ∀ pointer,registry.graph.valid pointer → graph.valid pointer := by intro pointer member; rw [validEq]; exact member
  have nodeFloor : 2713731432≤node.toNat := frontierLower.trans floor
  have finalChildren:=(children.finished source built registry.graph.valid node previous cursor data header bytes flag occupied owned.1 nodeFloor below above).enlarge
    post registry.graph.valid graph.valid node 16 includes
  have value:=branch_finished_value source built record db node previous header bytes flag cursor data index occupied item view payload selected dbUpper valid empty below above builtDomain
  have tags : ∀ pointer,registry.graph.valid pointer → pointer≠0#64 → wordAt post.memory pointer=wordAt source.memory pointer := by
    intro pointer member active
    unfold wordAt
    rw [agree pointer (.header pointer member active)]
  have currentExcluded:=excluded.of_agreement source.memory post.memory source.memaddrs post.memaddrs registry.graph graph node 176 validEq tags
  have stored : post.memory node=.word 3#64 :=
    (branch_finished_tag source built node previous data header bytes flag occupied).trans
      ((above node (by omega)).trans owned.2.2)
  obtain ⟨next,member,forward,backward⟩:=current.branch_result post frontier db heap node finalChildren value (domain.trans view.rows.domain)
    owned.1 owned.2.1 stored floor before currentExcluded
  refine ⟨next,member,?_,?_⟩
  · intro pointer member
    exact forward pointer (includes pointer member)
  · intro pointer member
    rcases backward pointer member with prior|fresh
    · left; rw [←validEq]; exact prior
    · exact Or.inr fresh

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_finished_outside_memory
#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.branch_finished
