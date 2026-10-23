import InitECandidate.Solver.Mpt.TriePathBufferInvalidate

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A genuine ignored invalidation retains all node/value/path models
and the independent current key buffer at the true caller continuation. -/
theorem Graph.invalidate_call_paths (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (owner key : BitVec 64) (length limit lower upper pathLower pathUpper : Nat)
    (graph : Graph source.memory source.memaddrs) (property : BitVec 64 → BitVec 64 → Prop) (values : Values graph limit property)
    (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower pathUpper) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower pathUpper key length)
    (member : graph.valid owner) (active : owner≠0#64) (arguments : List (Flapjack.Pancake.PanLang.ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some [.val (.word owner)])
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "node_invalidate") arguments)=(none,target)) :
    target={NodeInvalidate.post source owner with clock:=source.clock-1} ∧
      ∃ next : Graph target.memory target.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
        Nonempty (Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower pathUpper ∧ next.PathSeparated ∧
        next.PathBuffer target.be pathLower pathUpper key length := by
  have bounds:=regions owner member active
  have targetEq:=NodeInvalidate.call_normal source target owner arguments args installed domain
    (AllocatedBytes.Arena.weaken owner _ 32 bounds.2.1 (nodeBytes_bounds (wordAt source.memory owner)).1) bounds.2.2.1 normal
  refine ⟨targetEq,?_⟩
  rw [targetEq]
  obtain ⟨next,same,nextRegions,nextDisjoint,nextValues⟩:=graph.after_invalidate source owner limit lower upper property values regions disjoint member active
  obtain ⟨nextPaths,nextPathRegions,nextSeparated⟩:=graph.invalidate_path_models source owner lower upper pathLower pathUpper regions disjoint paths pathRegions separated member active next same
  exact ⟨next,same,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,
    buffer.after_invalidate source graph lower upper pathLower pathUpper key length regions disjoint owner member active next same⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.invalidate_call_paths
