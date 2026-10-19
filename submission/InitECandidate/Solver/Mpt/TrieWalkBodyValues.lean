import InitECandidate.Solver.Mpt.TrieWalkBranchValues
import InitECandidate.Solver.Mpt.TrieWalkExtensionValues
import InitECandidate.Solver.Mpt.TrieWalkCase

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.ReturnFacts

variable {property : BitVec 64 → BitVec 64 → Prop}

/-- A real returned body value is classified using the current closed graph
and its physical leaf/branch value slots. Comparisons may fail or time out;
no future outcome is assumed. -/
theorem Graph.loop_body_returns (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (valueLimit : Nat) (values : Values graph valueLimit property)
    (node : BitVec 64) (member : graph.valid node) (active : node≠0#64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word node)))
    (installed : Input.OriginalCode.Installed source.code) :
    Returns source loopBody (Answer source.memaddrs valueLimit (property:=property)) := by
  obtain ⟨mapped,stored⟩ := graph.header node member active
  have tagRead := node_field_read source node 0#64 (wordAt source.memory node) nodeCell (by simpa using mapped) (by simpa using stored)
  rw [loop_body_shape]
  refine Input.ReturnFacts.declared_word source "k" (nodeField 0#64) (wordAt source.memory node) afterK
    (Answer source.memaddrs valueLimit (property:=property)) tagRead ?_
  let entered := bind source "k" (wordAt source.memory node)
  have currentNode : entered.locals.lookup (ofString "node")=some (.val (.word node)) :=
    (bind_lookup_other source "k" "node" _ (by decide)).trans nodeCell
  have tagCell : entered.locals.lookup (ofString "k")=some (.val (.word (wordAt source.memory node))) := bind_lookup_same _ _ _
  intro post value normal
  rw [after_k_evaluate entered (wordAt source.memory node) installed tagCell] at normal
  split_ifs at normal with zero one two
  · have safe : Input.LocalPrefix (ofString "node") unresolved := .call none _ _ (by intro name impossible; cases impossible)
    exact Input.ReturnFacts.local_prefix entered (ofString "node") unresolved safe
      (Answer source.memaddrs valueLimit (property:=property)) post value normal
  · exact leaf_returns entered node valueLimit (values.leaf node member active one) currentNode installed post value normal
  · exact extension_returns entered source.memaddrs valueLimit post value normal
  · exact branch_returns entered node valueLimit (values.branch node member active zero one two) currentNode post value normal

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.loop_body_returns
