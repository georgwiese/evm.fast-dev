import InitECandidate.Solver.Mpt.TrieWalkLoopCost

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Complete unchanged trie_walk body, including actual pos initialization
and final return. This local bound still requires a reachable graph/key proof. -/
theorem Graph.body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (node nibs : BitVec 64) (limit : Nat)
    (key : KeyView source.memory source.memaddrs source.be nibs limit) (member : graph.valid node)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsCell : source.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (limitCell : source.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock - (evaluateHOLFiniteState source body).2.clock ≤ 2080 := by
  rw [body_shape]
  apply Input.ClockCost.declared_current source "pos" (.const 0#64) 0#64 _ 2080 (by rfl)
  let entered := bind source "pos" 0#64
  have currentNode : entered.locals.lookup (ofString "node") = some (.val (.word node)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans nodeCell
  have currentNibs : entered.locals.lookup (ofString "nibs") = some (.val (.word nibs)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans nibsCell
  have currentLimit : entered.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans limitCell
  have currentPos : entered.locals.lookup (ofString "pos") = some (.val (.word 0#64)) := bind_lookup_same _ _ _
  have cost := Graph.loop_cost_2080 entered graph node nibs 0#64 limit key member (by simp)
    currentNode currentNibs currentPos currentLimit installed
  have returned : Input.ClockCost.Bound entered.code afterLoop 0 := by
    rw [after_loop_shape]
    exact Input.ClockCost.returned entered.code _
  exact Input.ClockCost.sequence_current entered loop afterLoop 2080 0 cost returned

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.body_cost
