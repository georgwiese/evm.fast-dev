import InitECandidate.Solver.Mpt.WitnessCoreLoopInvariant
import InitECandidate.Solver.Mpt.WitnessBranchPending
import InitECandidate.Solver.Mpt.WitnessCompletedBranch
import InitECandidate.Solver.Mpt.WitnessCompletedExtension
import InitECandidate.Solver.Mpt.WitnessTerminalRegistration
import InitECandidate.Solver.Mpt.TrieGraphStorageFrame
import InitECandidate.Solver.Mpt.TrieGraphCacheFrame

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Completed nodes at the current real persistent heap, with closed
children, actual bounded values and disjoint original node allocations. -/
structure NodeRegistry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier : Nat) (heap db : BitVec 64) where
  graph : TrieWalk.Graph source.memory source.memaddrs
  values : TrieWalk.Values graph 1024 (WitnessValue db)
  regions : graph.Regions frontier heap.toNat
  disjoint : graph.Disjoint

def NodeRegistry.empty (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier : Nat) (heap db : BitVec 64) :
    NodeRegistry source frontier heap db :=
  ⟨TrieWalk.Graph.empty source.memory source.memaddrs,TrieWalk.Values.empty source.memory source.memaddrs 1024 (WitnessValue db),
    TrieWalk.Graph.Regions.empty source.memory source.memaddrs frontier heap.toNat,TrieWalk.Graph.Disjoint.empty source.memory source.memaddrs⟩

/-- Preserve exactly the old completed nodes through a genuine callee
frame, then extend only their actual upper heap frontier. -/
theorem NodeRegistry.after_normal_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap nextHeap db cursor limit : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (above : cursor.toNat≤frontier) (grows : heap.toNat≤nextHeap.toNat)
    (frame : WitnessDecode.NormalFrame source target heap cursor limit) :
    ∃ next : NodeRegistry target frontier nextHeap db,next.graph.valid=registry.graph.valid := by
  obtain ⟨graph,validEq,regions,disjoint,⟨values⟩⟩:=registry.graph.after_normal_frame source target 1024 frontier heap.toNat (WitnessValue db)
    registry.values registry.regions registry.disjoint heap cursor limit above (Nat.le_refl _) frame
  exact ⟨⟨graph,values,regions.weaken graph frontier heap.toNat frontier nextHeap.toNat (Nat.le_refl _) grows,disjoint⟩,validEq⟩

theorem NodeRegistry.after_cache (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db child hash : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (member : registry.graph.valid child) :
    ∃ next : NodeRegistry (returnCacheState source child hash) frontier heap db,next.graph.valid=registry.graph.valid := by
  obtain ⟨graph,validEq,regions,disjoint,⟨values⟩⟩:=registry.graph.after_cache source child hash 1024 frontier heap.toNat (WitnessValue db)
    registry.values registry.regions registry.disjoint member
  exact ⟨⟨graph,values,regions,disjoint⟩,validEq⟩

noncomputable def NodeRegistry.register (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db node : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (data : TrieWalk.Registration registry.graph node)
    (leaf : GasBudget.wordAt source.memory node=1#64 → TrieWalk.ValueView source.memory source.memaddrs node 48#64 56#64 1024 (WitnessValue db))
    (branch : GasBudget.wordAt source.memory node≠0#64 → GasBudget.wordAt source.memory node≠1#64 → GasBudget.wordAt source.memory node≠2#64 →
      TrieWalk.ValueView source.memory source.memaddrs node 160#64 168#64 1024 (WitnessValue db))
    (floor : frontier≤node.toNat) (arena : AllocatedBytes.Arena node (TrieWalk.nodeBytes (GasBudget.wordAt source.memory node)))
    (aligned : node.toNat%8=0) (before : node.toNat+TrieWalk.nodeBytes (GasBudget.wordAt source.memory node)≤heap.toNat)
    (excludes : registry.graph.Excludes node (TrieWalk.nodeBytes (GasBudget.wordAt source.memory node))) : NodeRegistry source frontier heap db :=
  ⟨registry.graph.register node data,TrieWalk.Values.register registry.graph node data 1024 registry.values leaf branch,
    registry.regions.register registry.graph node data frontier heap.toNat floor arena aligned before,
    registry.disjoint.register registry.graph node data (fun old member active _=>(excludes old member active).symm)⟩

namespace Stack

structure ActiveRegistry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier : Nat) (db : BitVec 64) (cfg : Configuration) where
  nodes : NodeRegistry source frontier cfg.heap db
  children : ChildViews source nodes.graph.valid cfg.stack
  excludes : ∀ entry∈cfg.stack,∀ node index occupied,entry.data.payload=.branch node index occupied → nodes.graph.Excludes node 176
  returned : cfg.phase=.returning → ∀ child,source.locals.lookup (ofString "result")=some (.val (.word child)) → nodes.graph.valid child

/-- Reachability data for the real materializer loop, extending the
already checked physical/control/rank invariant. -/
structure RichInvariant (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cfg : Configuration) : Prop where
  base : Invariant input frontier db limit source cfg
  registry : Nonempty (ActiveRegistry source frontier db cfg)

/-- The genuine empty-stack decoder entry needs no input-graph or future
callee hypothesis: its completed registry is the actual empty registry. -/
theorem RichInvariant.initial (input : Guest.InputBlob) (frontier : Nat) (db heap cursor limit : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (base : Invariant input frontier db limit source ⟨heap,cursor,[],.decode,true⟩) :
    RichInvariant input frontier db limit source ⟨heap,cursor,[],.decode,true⟩ := by
  refine ⟨base,⟨⟨NodeRegistry.empty source frontier heap db,ChildViews.empty source _,?_,?_⟩⟩⟩
  · intro entry member; cases member
  · intro phase; cases phase

end Stack
end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.after_normal_frame
#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.after_cache
#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.register
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.RichInvariant.initial
