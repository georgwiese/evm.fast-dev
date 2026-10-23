import InitECandidate.Solver.Mpt.WitnessCorePathFrame
import InitECandidate.Solver.Mpt.TriePathBytesSeparation

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Extending the actual current graph by a fresh node retains every
pending path. Any new path starts after the old allocation frontier;
old pending branches and completed nodes lie before that frontier. -/
theorem ActiveRegistry.PathModel.node_added (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db : BitVec 64) (cfg nextCfg : Configuration) (node : BitVec 64)
    (registry : ActiveRegistry source frontier db cfg) (next : ActiveRegistry source frontier db nextCfg)
    (paths : registry.PathModel) (nextPaths : next.nodes.PathModel) (stackEq : nextCfg.stack=cfg.stack)
    (records : ∀ current∈cfg.stack,WitnessRecord.View source current.record db current.data)
    (bounded : ∀ current∈cfg.stack,current.data.BeforeHeap cfg.heap.toNat)
    (members : ∀ owner,next.nodes.graph.valid owner → registry.nodes.graph.valid owner ∨ owner=node)
    (fresh : node≠0#64 → cfg.heap.toNat≤node.toNat)
    (allocation : node≠0#64 → AllocatedBytes.Arena node (TrieWalk.nodeBytes (wordAt source.memory node)))
    (newPath : node≠0#64 → (wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64) →
      cfg.heap.toNat≤(wordAt source.memory (node+32#64)).toNat ∧ (wordAt source.memory (node+32#64)).toNat%8=0) : next.PathModel := by
  refine ⟨nextPaths,?_,?_,?_,?_⟩
  · intro entry member
    rw [stackEq] at member
    exact paths.pending entry member
  · intro current member active tag index inside entry inStack owner slot occupied payload offset offsetInside
    rw [stackEq] at inStack
    rcases members current member with prior|same
    · exact paths.nodePending current prior active tag index inside entry inStack owner slot occupied payload offset offsetInside
    · subst current
      obtain ⟨floor,aligned⟩:=newPath active tag
      have span:=nextPaths.bytes.span node member active tag
      have before:=(bounded entry inStack).2
      simp only [payload,WitnessRecord.Payload.endAddress] at before
      have arena:=(records entry inStack).owned
      simp only [payload,WitnessRecord.Payload.Owned] at arena
      exact span.apart_after source.memory source.memaddrs source.be _ owner _ 176 aligned arena.1 (before.trans floor) index inside offset offsetInside
  · intro entry inStack pointer length payload index inside owner member active offset offsetInside
    rw [stackEq] at inStack
    rcases members owner member with prior|same
    · exact paths.pendingNode entry inStack pointer length payload index inside owner prior active offset offsetInside
    · subst owner
      have span:=paths.pending entry inStack
      simp only [payload,WitnessRecord.Payload.PathBytes] at span
      have before:=(bounded entry inStack).2
      simp only [payload,WitnessRecord.Payload.endAddress] at before
      exact span.1.apart_before source.memory source.memaddrs source.be pointer node length.toNat _ (allocation active)
        (before.trans (fresh active)) index inside offset offsetInside
  · intro entry inStack pointer length payload index inside other otherIn owner slot occupied ownerPayload offset offsetInside
    rw [stackEq] at inStack otherIn
    exact paths.pendingPending entry inStack pointer length payload index inside other otherIn owner slot occupied ownerPayload offset offsetInside

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.PathModel.node_added
