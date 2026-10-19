import InitECandidate.Solver.Mpt.TrieWalkBranch
import InitECandidate.Solver.Input.ScalarAssignNormal

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def branchNodeExpression : ExpHOL 64 := match branchNode with | .assign _ _ expression => expression | _ => .const 0#64

set_option maxRecDepth 10000 in
theorem branch_node_shape : branchNode = .assign .local (ofString "node") branchNodeExpression := by
  simp only [branchNode, branchAdvance, branch, nodeStep, afterHash, afterK, loopBody, loop, afterPos, body,
    Guest.guestFn_trie_walk, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, branchNodeExpression]

/-- A real branch derives the actual child-word read and exact two local
updates. The later topology proof can identify this observed child read. -/
theorem branch_node_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node position limit : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (limitCell : source.locals.lookup (ofString "nlen") = some (.val (.word limit)))
    (normal : evaluateHOLFiniteState source branch = (none, post)) :
    ∃ nextNode : BitVec 64, eval source branchNodeExpression = some (.val (.word nextNode)) ∧
      post = bind (bind source "node" nextNode) "pos" (position + 1#64) := by
  rw [branch_shape] at normal
  obtain ⟨middle, guardRun, advanceRun⟩ := Input.sequence_none source post branchGuard branchAdvance normal
  obtain ⟨different, middleEq⟩ := branch_guard_normal source middle position limit posCell limitCell guardRun
  subst middle
  rw [branch_advance_shape] at advanceRun
  obtain ⟨assigned, nodeRun, posRun⟩ := Input.sequence_none source post branchNode branchPosition advanceRun
  rw [branch_node_shape] at nodeRun
  obtain ⟨nextNode, read, assignedEq⟩ := Input.scalar_assign_none source assigned "node" branchNodeExpression node nodeCell nodeRun
  have currentPosition : assigned.locals.lookup (ofString "pos") = some (.val (.word position)) := by
    rw [assignedEq]
    exact (bind_lookup_other _ _ _ _ (by decide)).trans posCell
  have posRead : eval assigned (addConst (localVar "pos") 1#64) = some (.val (.word (position + 1#64))) := by
    simp [eval, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, currentPosition, valueIsWord, valueWord, wordOpHOL, wordOp]
  have postEq := Input.assign_none assigned post "pos" (addConst (localVar "pos") 1#64) (position + 1#64) posRead posRun
  exact ⟨nextNode, read, by rw [postEq, assignedEq]⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.branch_node_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.branch_node_normal
