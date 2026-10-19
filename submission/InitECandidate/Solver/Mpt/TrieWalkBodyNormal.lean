import InitECandidate.Solver.Mpt.TrieWalkCase
import InitECandidate.Solver.Mpt.TrieWalkGraphExtension
import InitECandidate.Solver.Mpt.TrieWalkGraphBranch
import InitECandidate.Solver.WitnessRadix.RestoreLookup

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem loop_body_readonly (code) (installed : Input.OriginalCode.Installed code) : Input.LocalEffects.Preserves code loopBody := by
  simp only [loopBody, loop, afterPos, body, Guest.guestFn_trie_walk, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]
  repeat first
    | apply Input.LocalEffects.sequence
    | apply Input.LocalEffects.declared
    | apply Input.LocalEffects.conditional
    | exact Input.LocalEffects.assign code _ _
    | exact Input.LocalEffects.returned code _
    | exact Input.LocalEffects.skip code
    | exact Input.LocalEffects.call_body code (some none) (ofString "mpt_fail") _ Fail.formals Fail.body .one
        (Fail.original_code code installed) (Fail.readonly code)
    | apply Input.LocalEffects.scoped_body code (ofString "eq") .one (ofString "memeq") _ _ WitnessRadix.Memeq32.formals WitnessRadix.Memeq32.body .one
        (memeq_code code installed) (memeq_readonly code)
    | apply Input.LocalEffects.scoped_body code (ofString "eq2") .one (ofString "memeq") _ _ WitnessRadix.Memeq32.formals WitnessRadix.Memeq32.body .one
        (memeq_code code installed) (memeq_readonly code)

/-- Every actual fall-through body selects a closed physical child and
strictly decreases the phase rank. Leaf/hash visits cannot fall through. -/
theorem Graph.loop_body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (node nibs position : BitVec 64) (limit : Nat)
    (key : KeyView source.memory source.memaddrs source.be nibs limit)
    (member : graph.valid node) (active : node ≠ 0#64) (bounded : position.toNat ≤ limit)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsCell : source.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (limitCell : source.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))))
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source loopBody = (none, post)) :
    ∃ nextNode nextPosition, graph.valid nextNode ∧ nextPosition.toNat ≤ limit ∧
      post.locals.lookup (ofString "node") = some (.val (.word nextNode)) ∧
      post.locals.lookup (ofString "pos") = some (.val (.word nextPosition)) ∧
      Rank.value limit post.memory nextNode nextPosition < Rank.value limit source.memory node position := by
  obtain ⟨mapped, stored⟩ := graph.header node member active
  have tagRead := node_field_read source node 0#64 (wordAt source.memory node) nodeCell (by simpa using mapped) (by simpa using stored)
  rw [loop_body_shape] at normal
  obtain ⟨inner, tailRun, scope⟩ := Input.declaration_none source post "k" (nodeField 0#64) (wordAt source.memory node) _ tagRead normal
  let entered := bind source "k" (wordAt source.memory node)
  change evaluateHOLFiniteState entered afterK = (none, inner) at tailRun
  have currentNode : entered.locals.lookup (ofString "node") = some (.val (.word node)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans nodeCell
  have currentNibs : entered.locals.lookup (ofString "nibs") = some (.val (.word nibs)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans nibsCell
  have currentPos : entered.locals.lookup (ofString "pos") = some (.val (.word position)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans posCell
  have currentLimit : entered.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans limitCell
  have tagCell : entered.locals.lookup (ofString "k") = some (.val (.word (wordAt source.memory node))) := bind_lookup_same _ _ _
  have finish : ∀ nextNode nextPosition, graph.valid nextNode → nextPosition.toNat ≤ limit →
      inner.locals.lookup (ofString "node") = some (.val (.word nextNode)) →
      inner.locals.lookup (ofString "pos") = some (.val (.word nextPosition)) →
      Rank.value limit inner.memory nextNode nextPosition < Rank.value limit source.memory node position →
      ∃ nextNode nextPosition, graph.valid nextNode ∧ nextPosition.toNat ≤ limit ∧
        post.locals.lookup (ofString "node") = some (.val (.word nextNode)) ∧
        post.locals.lookup (ofString "pos") = some (.val (.word nextPosition)) ∧
        Rank.value limit post.memory nextNode nextPosition < Rank.value limit source.memory node position := by
    intro nextNode nextPosition valid nextBounded nodeInner posInner smaller
    refine ⟨nextNode, nextPosition, valid, nextBounded, ?_, ?_, ?_⟩
    · rw [scope, restore_lookup_other source inner "k" "node" (by decide)]
      exact nodeInner
    · rw [scope, restore_lookup_other source inner "k" "pos" (by decide)]
      exact posInner
    · simpa only [scope, restore] using smaller
  rw [after_k_evaluate entered (wordAt source.memory node) installed tagCell] at tailRun
  split_ifs at tailRun with zero one two
  · exact (Fail.call_not_normal entered inner installed [.const 2#64] tailRun).elim
  · exact (leaf_stops entered (congrArg Prod.fst tailRun)).elim
  · obtain ⟨paid, nextNode, nextPosition, positive, cost, funded, valid, nextBounded, innerEq, smaller⟩ :=
      Graph.extension_normal entered inner graph node nibs position limit key member active two bounded
        currentNode currentNibs currentPos currentLimit (memeq_code source.code installed) tailRun
    apply finish nextNode nextPosition valid nextBounded _ _ smaller
    · rw [innerEq]
      exact bind_lookup_same _ _ _
    · rw [innerEq]
      exact (bind_lookup_other _ _ _ _ (by decide)).trans (bind_lookup_same _ _ _)
  · obtain ⟨nextNode, nextPosition, valid, nextBounded, innerEq, smaller⟩ :=
      Graph.branch_normal entered inner graph node nibs position limit key member active zero one two bounded
        currentNode currentNibs currentPos currentLimit tailRun
    apply finish nextNode nextPosition valid nextBounded _ _ smaller
    · rw [innerEq]
      exact (bind_lookup_other _ _ _ _ (by decide)).trans (bind_lookup_same _ _ _)
    · rw [innerEq]
      exact bind_lookup_same _ _ _

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.loop_body_readonly
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.loop_body_normal
