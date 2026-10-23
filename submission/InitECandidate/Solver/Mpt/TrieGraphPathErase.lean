import InitECandidate.Solver.Mpt.TrieGraphStorageFrame
import InitECandidate.Solver.Mpt.TriePathBuffer
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget

/-- Pure calls and lexical changes retain the entire actual graph and
all full path models, with independent node and path lifetime bounds. -/
theorem Graph.after_erase (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (limit lower upper pathLower pathUpper : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : Values graph limit property) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower pathUpper) (separated : graph.PathSeparated)
    (frame : Input.LocalEffects.erase target=Input.LocalEffects.erase source) :
    ∃ next : Graph target.memory target.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧ Nonempty (Values next limit property) ∧
      next.PathBytes target.be ∧ next.PathRegions pathLower pathUpper ∧ next.PathSeparated := by
  have memory:=congrArg PanSemStateFiniteExact.memory frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  have endian:=congrArg PanSemStateFiniteExact.be frame
  change target.memory=source.memory at memory
  change target.memaddrs=source.memaddrs at domain
  change target.be=source.be at endian
  have agree : ∀ query,graph.Footprint query → target.memory query=source.memory query:=by intro query required; rw [memory]
  obtain ⟨next,same,nextRegions,nextDisjoint,nextValues⟩:=graph.after_agreement source target limit lower upper property values regions disjoint domain agree
    (by intro query required; rw [memory])
  exact ⟨next,same,nextRegions,nextDisjoint,nextValues,
    paths.of_agreement source.memory target.memory source.memaddrs target.memaddrs source.be target.be graph next same domain endian agree
      (by intro node member active tag index inside; rw [memory]),
    pathRegions.of_agreement source.memory target.memory source.memaddrs target.memaddrs graph next pathLower pathUpper same agree,
    separated.of_agreement source.memory target.memory source.memaddrs target.memaddrs graph next same agree⟩

theorem Graph.PathBuffer.of_erase (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (next : Graph target.memory target.memaddrs)
    (lower upper : Nat) (pointer : BitVec 64) (length : Nat) (buffer : graph.PathBuffer source.be lower upper pointer length)
    (same : next.valid=graph.valid) (frame : Input.LocalEffects.erase target=Input.LocalEffects.erase source) :
    next.PathBuffer target.be lower upper pointer length := by
  have memory:=congrArg PanSemStateFiniteExact.memory frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  have endian:=congrArg PanSemStateFiniteExact.be frame
  change target.memory=source.memory at memory
  change target.memaddrs=source.memaddrs at domain
  change target.be=source.be at endian
  refine ⟨buffer.span.of_agreement source.memory target.memory source.memaddrs target.memaddrs source.be target.be pointer length domain endian
    (by intro index inside; rw [memory]),buffer.bounds,?_⟩
  intro index inside owner member active offset within
  have oldMember : graph.valid owner:=by rwa [same] at member
  rw [memory] at within
  exact buffer.apart index inside owner oldMember active offset within

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.after_erase
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathBuffer.of_erase
