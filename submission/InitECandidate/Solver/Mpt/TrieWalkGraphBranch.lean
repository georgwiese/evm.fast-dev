import InitECandidate.Solver.Mpt.TrieWalkMemory

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 10000 in
theorem branch_node_expression_shape : branchNodeExpression = .load .one (.op .add
    [localVar "node", .const 32#64, .panop .mul [.loadByte pathAtPosition, .const 8#64]]) := by
  simp only [branchNodeExpression, branchNode, branchAdvance, branch, nodeStep, afterHash, afterK, loopBody, loop, afterPos, body,
    Guest.guestFn_trie_walk, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, localVar, pathAtPosition]

theorem branch_node_read (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node nibs position child : BitVec 64) (nibble : UInt8)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsCell : source.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (byteRead : @panMemLoadByteHOL 64 _ source.memory source.memaddrs
      (fun address => Classical.propDecidable (source.memaddrs address)) source.be (nibs + position) = some nibble)
    (mapped : source.memaddrs (node + 32#64 + BitVec.ofNat 64 (nibble.toNat * 8)))
    (stored : source.memory (node + 32#64 + BitVec.ofNat 64 (nibble.toNat * 8)) = .word child) :
    eval source branchNodeExpression = some (.val (.word child)) := by
  have product : BitVec.ofNat 64 nibble.toNat * 8#64 = BitVec.ofNat 64 (nibble.toNat * 8) := by
    rw [BitVec.ofNat_mul]
  simp [branch_node_expression_shape, eval, localVar, pathAtPosition, evalHOLExact, evalListHOLExact, toExact,
    nodeCell, nibsCell, posCell, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
    byteRead, product, memLoadHOLExact, isWfShapeExactHOL, ← BitVec.add_assoc, mapped, stored]

/-- A real continuing branch selects one of the actual sixteen mapped
children using a current key nibble, and strictly decreases the path rank. -/
theorem Graph.branch_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (node nibs position : BitVec 64) (limit : Nat)
    (key : KeyView source.memory source.memaddrs source.be nibs limit)
    (member : graph.valid node) (active : node ≠ 0#64)
    (notHash : wordAt source.memory node ≠ 0#64) (notLeaf : wordAt source.memory node ≠ 1#64)
    (notExtension : wordAt source.memory node ≠ 2#64) (bounded : position.toNat ≤ limit)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsCell : source.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (limitCell : source.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))))
    (normal : evaluateHOLFiniteState source TrieWalk.branch = (none, post)) :
    ∃ nextNode nextPosition, graph.valid nextNode ∧ nextPosition.toNat ≤ limit ∧
      post = bind (bind source "node" nextNode) "pos" nextPosition ∧
      Rank.value limit post.memory nextNode nextPosition < Rank.value limit source.memory node position := by
  obtain ⟨inside, advanced, number, fields⟩ := TrieWalk.branch_normal source post position limit key.small bounded posCell limitCell normal
  obtain ⟨nextNode, childRead, postEq⟩ := branch_node_normal source post node position (BitVec.ofNat 64 limit) nodeCell posCell limitCell normal
  obtain ⟨nibble, smallNibble, byteRead⟩ := key.nibble position.toNat inside
  have address : byteAddress nibs position.toNat = nibs + position := by simp [byteAddress]
  rw [address] at byteRead
  let child := graph.branch node member active notHash notLeaf notExtension nibble.toNat smallNibble
  have observed := branch_node_read source node nibs position child.child nibble nodeCell nibsCell posCell byteRead child.mapped child.stored
  have nextEq : nextNode = child.child := by
    have same := childRead.symm.trans observed
    simpa only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using same
  subst nextNode
  refine ⟨child.child, position + 1#64, child.member, by omega, postEq, ?_⟩
  exact Rank.branch_decreases source post node child.child position limit active key.small bounded posCell limitCell normal

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.branch_node_expression_shape
#print axioms InitECandidate.Solver.Mpt.TrieWalk.branch_node_read
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.branch_normal
