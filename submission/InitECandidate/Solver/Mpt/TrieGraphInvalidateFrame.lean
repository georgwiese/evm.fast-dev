import InitECandidate.Solver.Mpt.TrieGraphCacheOffsets
import InitECandidate.Solver.Mpt.TrieGraphStorageFrame
import InitECandidate.Solver.Mpt.NodeInvalidateCall

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- The original three cache clears retain the entire closed graph, real
value fields and disjoint allocation geometry. Shared children are allowed. -/
theorem Graph.after_invalidate (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (owner : BitVec 64) (graph : Graph source.memory source.memaddrs)
    (limit lower upper : Nat) (property : BitVec 64→BitVec 64→Prop) (values : Values graph limit property)
    (regions : graph.Regions lower upper) (disjoint : graph.Disjoint) (member : graph.valid owner) (active : owner≠0#64) :
    let post:=NodeInvalidate.post source owner
    ∃ next : Graph post.memory post.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
      Nonempty (Values next limit property) := by
  let post:=NodeInvalidate.post source owner
  apply Graph.after_agreement source post graph limit lower upper property values regions disjoint rfl
  · intro query required
    obtain ⟨node,offset,nodeMember,nodeActive,inside,data,equal⟩:=required.data_location graph query
    apply NodeInvalidate.post_away source owner query
    all_goals
      rw [equal]
      exact graph.cache_field_away lower upper regions disjoint owner node offset _ (by decide) (by decide)
        member active nodeMember nodeActive inside data
  · intro query required
    obtain ⟨node,offset,nodeMember,nodeActive,inside,data,equal⟩:=required.data_location graph query
    apply NodeInvalidate.post_away source owner query
    all_goals
      rw [equal]
      exact graph.cache_field_away lower upper regions disjoint owner node offset _ (by decide) (by decide)
        member active nodeMember nodeActive inside data

/-- The same graph/value preservation at the genuine original ignored
caller, deriving its node mapping from the registered allocation. -/
theorem Graph.after_invalidate_call (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (owner : BitVec 64) (graph : Graph source.memory source.memaddrs)
    (limit lower upper : Nat) (property : BitVec 64→BitVec 64→Prop) (values : Values graph limit property)
    (regions : graph.Regions lower upper) (disjoint : graph.Disjoint) (member : graph.valid owner) (active : owner≠0#64)
    (arguments : List (Flapjack.Pancake.PanLang.ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some [.val (.word owner)])
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) (Flapjack.Basis.Pure.MlString.ofString "node_invalidate") arguments)=(none,target)) :
    ∃ next : Graph target.memory target.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
      Nonempty (Values next limit property) := by
  obtain ⟨floor,arena,aligned,before⟩:=regions owner member active
  have targetEq:=NodeInvalidate.call_normal source target owner arguments args installed domain
    (AllocatedBytes.Arena.weaken owner _ 32 arena (nodeBytes_bounds (wordAt source.memory owner)).1) aligned normal
  rw [targetEq]
  exact graph.after_invalidate source owner limit lower upper property values regions disjoint member active

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.after_invalidate
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.after_invalidate_call
