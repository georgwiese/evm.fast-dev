import InitECandidate.Solver.Mpt.TrieGraphPathPrefix
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- A current upper bound on the complete stored paths, including bytes
beyond the finite search key. This concerns current memory only. -/
def Graph.PathLimit {memory : Memory} {domain : BitVec 64 → Prop} (graph : Graph memory domain) (maximum : Nat) : Prop:=
  ∀ node,graph.valid node → node≠0#64 → (wordAt memory node=1#64 ∨ wordAt memory node=2#64) →
    (wordAt memory (node+40#64)).toNat≤maximum

theorem Graph.PathLimit.of_regions {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.PathRegions lower upper) : graph.PathLimit (upper-lower) := by
  intro node member active tag
  have bounds:=regions node member active tag
  omega

theorem Graph.PathLimit.of_erase (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (next : Graph target.memory target.memaddrs) (maximum : Nat)
    (limit : graph.PathLimit maximum) (same : next.valid=graph.valid)
    (frame : Input.LocalEffects.erase target=Input.LocalEffects.erase source) : next.PathLimit maximum := by
  have memory:=Input.LocalEffects.memory_of_erase source target frame
  intro node member active tag
  have oldMember : graph.valid node:=by rwa [same] at member
  rw [memory] at tag ⊢
  exact limit node oldMember active tag

/-- A real frame before a fresh allocation retains the exact old path
limit when the registry itself is unchanged. -/
theorem Graph.PathLimit.of_prefix (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (next : Graph target.memory target.memaddrs) (lower upper maximum : Nat)
    (regions : graph.Regions lower upper) (limit : graph.PathLimit maximum) (same : next.valid=graph.valid)
    (memory : ∀ query : BitVec 64,query.toNat<upper → target.memory query=source.memory query) : next.PathLimit maximum := by
  intro node member active tag
  have oldMember : graph.valid node:=by rwa [same] at member
  have before : node.toNat<upper:=by
    have endBefore:=(regions node oldMember active).2.2.2
    have size:=nodeBytes_bounds (wordAt source.memory node)
    omega
  have tagEq : wordAt target.memory node=wordAt source.memory node:=congrArg MemoryBytes.wordBits (memory node before)
  have oldTag : wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64:=by rwa [tagEq] at tag
  have inside : 40<nodeBytes (wordAt source.memory node):=by
    rcases oldTag with one|two
    · rw [one]; decide
    · rw [two]; decide
  have fieldBefore : (node+40#64).toNat<upper:=by
    simpa only [byteAddress] using (graph.region_query_bounds lower upper regions node 40 oldMember active inside).2
  have sizeEq : wordAt target.memory (node+40#64)=wordAt source.memory (node+40#64):=congrArg MemoryBytes.wordBits (memory _ fieldBefore)
  rw [sizeEq]
  exact limit node oldMember active oldTag

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathLimit.of_regions
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathLimit.of_erase
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathLimit.of_prefix
