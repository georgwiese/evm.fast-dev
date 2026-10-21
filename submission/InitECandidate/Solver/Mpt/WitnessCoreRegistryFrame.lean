import InitECandidate.Solver.Mpt.WitnessCoreRegistryTerminal
import InitECandidate.Solver.Mpt.TrieGraphExclusion

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

theorem NodeRegistry.tags_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db cursor limit : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (above : cursor.toNat≤frontier) (frame : WitnessDecode.NormalFrame source target heap cursor limit) :
    ∀ node,registry.graph.valid node → node≠0#64 → wordAt target.memory node=wordAt source.memory node := by
  intro node member active
  have bounds:=registry.graph.footprint_bounds frontier heap.toNat registry.regions node (.header node member active)
  unfold wordAt
  rw [frame.memory node (above.trans bounds.1) bounds.2]

theorem NodeRegistry.tags_database (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (above : 2713717616≤frontier) (frame : DatabaseFrame source target heap) :
    ∀ node,registry.graph.valid node → node≠0#64 → wordAt target.memory node=wordAt source.memory node := by
  intro node member active
  have bounds:=registry.graph.footprint_bounds frontier heap.toNat registry.regions node (.header node member active)
  unfold wordAt
  rw [frame.memory node (above.trans bounds.1) bounds.2]

namespace Stack

/-- Old pending branches precede the incoming real heap. A new completed
result at or after that heap preserves all their allocation exclusions. -/
theorem ActiveRegistry.excludes_extension (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db : BitVec 64) (cfg : Configuration) (registry : ActiveRegistry source frontier db cfg)
    (view : View source db cfg.cursor.toNat cfg.heap.toNat cfg.stack)
    (next : TrieWalk.Graph target.memory target.memaddrs) (result : BitVec 64)
    (members : ∀ node,next.valid node → registry.nodes.graph.valid node ∨ node=result)
    (tags : ∀ node,registry.nodes.graph.valid node → node≠0#64 → wordAt target.memory node=wordAt source.memory node)
    (fresh : result≠0#64 → cfg.heap.toNat≤result.toNat) :
    ∀ entry∈cfg.stack,∀ node index occupied,entry.data.payload=.branch node index occupied → next.Excludes node 176 := by
  intro entry member node index occupied payload
  have before:=view.before entry member
  have mark:=view.marks entry member
  have nodeBefore : node.toNat+176≤cfg.heap.toNat := by
    have bound:=before.2
    simp only [payload,WitnessRecord.Payload.endAddress] at bound
    omega
  exact (registry.excludes entry member node index occupied payload).after_extension source.memory target.memory source.memaddrs target.memaddrs
    registry.nodes.graph next node result 176 members tags (fun active=>nodeBefore.trans (fresh active))

theorem ActiveRegistry.excludes_same (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db : BitVec 64) (cfg : Configuration) (registry : ActiveRegistry source frontier db cfg)
    (next : TrieWalk.Graph target.memory target.memaddrs) (validEq : next.valid=registry.nodes.graph.valid)
    (tags : ∀ node,registry.nodes.graph.valid node → node≠0#64 → wordAt target.memory node=wordAt source.memory node) :
    ∀ entry∈cfg.stack,∀ node index occupied,entry.data.payload=.branch node index occupied → next.Excludes node 176 := by
  intro entry member node index occupied payload
  exact (registry.excludes entry member node index occupied payload).of_agreement source.memory target.memory source.memaddrs target.memaddrs
    registry.nodes.graph next node 176 validEq tags

/-- The real resolver database-band frame includes all persistent child
and empty-value fields, while permitting its actual HASH scratch write. -/
theorem ActiveRegistry.children_database (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db : BitVec 64) (cfg : Configuration) (registry : ActiveRegistry source frontier db cfg)
    (view : View source db cfg.cursor.toNat cfg.heap.toNat cfg.stack)
    (next : TrieWalk.Graph target.memory target.memaddrs)
    (includes : ∀ node,registry.nodes.graph.valid node → next.valid node) (frame : DatabaseFrame source target cfg.heap) :
    ChildViews target next.valid cfg.stack := by
  apply registry.children.frame source target registry.nodes.graph.valid next.valid db cfg.cursor.toNat cfg.heap.toNat cfg.stack view includes
  intro entry member query lower upper
  have floor:=(view.records entry member).payloadFloor
  have mark:=view.marks entry member
  exact frame.memory query (by omega) (by omega)

end Stack
end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.tags_normal
#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.tags_database
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.excludes_extension
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.excludes_same
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.children_database
