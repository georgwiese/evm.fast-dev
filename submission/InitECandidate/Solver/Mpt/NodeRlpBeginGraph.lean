import InitECandidate.Solver.Mpt.NodeRlpBeginHeap
import InitECandidate.Solver.Mpt.TrieGraphPathBand
import InitECandidate.Solver.Mpt.TrieGraphPathFieldsFrame

namespace InitECandidate.Solver.Mpt.NodeRlpBegin
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget

theorem frame_field_before (frame : BitVec 64) (cutoff offset : Nat) (below : frame.toNat+48≤cutoff) (inside : offset≤40) :
    (frame+BitVec.ofNat 64 offset).toNat<cutoff := by
  have number : (frame+BitVec.ofNat 64 offset).toNat≤frame.toNat+offset:=by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show offset<2^64 by omega)]
    exact Nat.mod_le _ _
  omega

theorem Output.persistent_memory {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {limit allowance cutoff : Nat} {value : ValueHOL 64} (output : Output source target node heap frame limit value allowance)
    (below : frame.toNat+48≤cutoff) (query : BitVec 64) (above : cutoff≤query.toNat) (older : query.toNat<heap.toNat) :
    target.memory query=source.memory query := by
  apply output.older query older
  all_goals
    intro same
    have number:=congrArg BitVec.toNat same
    first
    | have before:=frame_field_before frame cutoff 24 below (by decide); omega
    | have before:=frame_field_before frame cutoff 32 below (by decide); omega
    | have before:=frame_field_before frame cutoff 40 below (by decide); omega

/-- Real begin preserves the same complete trie registry and full stored
paths above its actual low scratch frame. Current heap growth supplies the
new upper frontier. Existing cache words also survive the raw band frame. -/
theorem Output.graph_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {node heap frame : BitVec 64}
    {limit lower pathLower allowance cutoff : Nat} {property : BitVec 64→BitVec 64→Prop} {value : ValueHOL 64}
    (output : Output source target node heap frame limit value allowance) (data : Entry source node heap lower limit property)
    (disjoint : data.graph.Disjoint) (paths : data.graph.PathBytes source.be) (pathRegions : data.graph.PathRegions pathLower heap.toNat)
    (separated : data.graph.PathSeparated) (aligned : cutoff%8=0) (nodesAbove : cutoff≤lower) (pathsAbove : cutoff≤pathLower)
    (frameBelow : frame.toNat+48≤cutoff) :
    data.graph.PathFields target.memory ∧
      ∃ next : TrieWalk.Graph target.memory target.memaddrs,next.valid=data.graph.valid ∧ next.Regions lower (outputHeap source node heap).toNat ∧ next.Disjoint ∧
        Nonempty (TrieWalk.Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower (outputHeap source node heap).toNat ∧ next.PathSeparated := by
  have band:=output.persistent_memory frameBelow
  have fields : data.graph.PathFields target.memory:=TrieWalk.Graph.PathFields.of_agreement data.graph target.memory (by
    intro query required
    have bounds:=data.graph.footprint_bounds lower heap.toNat data.regions query required
    exact band query (nodesAbove.trans bounds.1) bounds.2)
  obtain ⟨next,same,regions,nextDisjoint,values,nextPaths,nextPathRegions,nextSeparated⟩:=data.graph.after_path_band source target limit lower pathLower heap.toNat cutoff property
    data.values data.regions disjoint paths pathRegions separated aligned nodesAbove pathsAbove output.domain output.endian band
  have heapFacts:=output.heap data
  refine ⟨fields,next,same,?_,nextDisjoint,values,nextPaths,?_,nextSeparated⟩
  · exact TrieWalk.Graph.Regions.weaken next lower heap.toNat lower (outputHeap source node heap).toNat regions (Nat.le_refl _) heapFacts.2.1
  · intro owner member active tag
    obtain ⟨before,after⟩:=nextPathRegions owner member active tag
    exact ⟨before,after.trans heapFacts.2.1⟩

end InitECandidate.Solver.Mpt.NodeRlpBegin

#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.frame_field_before
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Output.persistent_memory
#print axioms InitECandidate.Solver.Mpt.NodeRlpBegin.Output.graph_frame
