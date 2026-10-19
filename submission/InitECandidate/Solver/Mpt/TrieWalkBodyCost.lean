import InitECandidate.Solver.Mpt.TrieWalkCase
import InitECandidate.Solver.Mpt.TrieWalkGraphExtension
import InitECandidate.Solver.Mpt.TrieWalkLeaf

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The entire literal original loop body costs at most fifteen source
call/loop ticks at a current physical graph/key cursor, for every outcome. -/
theorem Graph.loop_body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (node nibs position : BitVec 64) (limit : Nat)
    (key : KeyView source.memory source.memaddrs source.be nibs limit)
    (member : graph.valid node) (active : node ≠ 0#64) (bounded : position.toNat ≤ limit)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsCell : source.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (limitCell : source.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))))
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock - (evaluateHOLFiniteState source loopBody).2.clock ≤ 15 := by
  obtain ⟨mapped, stored⟩ := graph.header node member active
  have tagRead := node_field_read source node 0#64 (wordAt source.memory node) nodeCell (by simpa using mapped) (by simpa using stored)
  rw [loop_body_shape]
  apply Input.ClockCost.declared_current source "k" (nodeField 0#64) (wordAt source.memory node) _ 15 tagRead
  let entered := bind source "k" (wordAt source.memory node)
  change entered.clock - (evaluateHOLFiniteState entered afterK).2.clock ≤ 15
  have currentNode : entered.locals.lookup (ofString "node") = some (.val (.word node)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans nodeCell
  have currentNibs : entered.locals.lookup (ofString "nibs") = some (.val (.word nibs)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans nibsCell
  have currentPos : entered.locals.lookup (ofString "pos") = some (.val (.word position)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans posCell
  have currentLimit : entered.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans limitCell
  have tagCell : entered.locals.lookup (ofString "k") = some (.val (.word (wordAt source.memory node))) := bind_lookup_same _ _ _
  rw [after_k_evaluate entered (wordAt source.memory node) installed tagCell]
  split_ifs with zero one two
  · have cost := Fail.call_price entered.code installed [.const 2#64] entered rfl
    change entered.clock - (evaluateHOLFiniteState entered unresolved).2.clock ≤ 1 at cost
    omega
  · exact Graph.leaf_cost entered graph node nibs position limit key member active one bounded
      currentNode currentNibs currentPos currentLimit (memeq_code source.code installed)
  · exact Graph.extension_cost entered graph node nibs position limit key member active two bounded
      currentNode currentNibs currentPos currentLimit (memeq_code source.code installed)
  · have clock := (branch_effects entered.code).2 entered rfl
    rw [clock]
    omega

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.loop_body_cost
