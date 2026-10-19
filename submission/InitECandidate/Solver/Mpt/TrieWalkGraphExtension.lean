import InitECandidate.Solver.Mpt.TrieWalkMemory

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- Actual extension progress and price under current physical graph/key
facts. Graph reachability is not asserted by this local theorem. -/
theorem Graph.extension_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (node nibs position : BitVec 64) (limit : Nat)
    (key : KeyView source.memory source.memaddrs source.be nibs limit)
    (member : graph.valid node) (active : node ≠ 0#64) (tag : wordAt source.memory node = 2#64)
    (bounded : position.toNat ≤ limit)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsCell : source.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (limitCell : source.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))))
    (code : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (normal : evaluateHOLFiniteState source TrieWalk.extension = (none, post)) :
    ∃ paid nextNode nextPosition, 1 ≤ paid ∧ paid ≤ 15 ∧ paid ≤ source.clock ∧
      graph.valid nextNode ∧ nextPosition.toNat ≤ limit ∧
      post = bind (bind {source with clock := source.clock - paid} "pos" nextPosition) "node" nextNode ∧
      Rank.value limit post.memory nextNode nextPosition < Rank.value limit source.memory node position := by
  let path := graph.path node member active (Or.inr tag)
  let child := graph.extension node member active tag
  obtain ⟨paid, positive, cost, funded, within, addition, nextBounded, postEq⟩ :=
    TrieWalk.extension_normal source post node nibs position path.size path.pointer child.child limit key.small bounded
      nodeCell nibsCell posCell limitCell path.sizeMapped path.sizeStored path.pointerMapped path.pointerStored
      child.mapped child.stored path.fits
      (fun within => KeyView.window_fits source.memory source.memaddrs source.be nibs position limit path.size.toNat key bounded within)
      path.mapped
      (fun within => KeyView.window_mapped source.memory source.memaddrs source.be nibs position limit path.size.toNat key bounded within)
      code normal
  have price := MemeqSmall.price_le_fourteen path.size.toNat (by have small := key.small; omega)
  refine ⟨paid, child.child, position + path.size, positive, by omega, funded, child.member, nextBounded, postEq, ?_⟩
  have memoryEq : post.memory = source.memory := by rw [postEq]; rfl
  by_cases zero : path.size = 0#64
  · have sizeWord : wordAt source.memory (node + 40#64) = 0#64 := (PathView.size_word source.memory source.memaddrs node path).trans zero
    have next := graph.zeroHop node member active tag sizeWord
    rw [memoryEq, zero, BitVec.add_zero]
    exact Rank.zero_extension limit source.memory source.memory node child.child position active tag next
  · have sizePositive : 0 < path.size.toNat := by
      by_contra notPositive
      apply zero
      apply BitVec.eq_of_toNat_eq
      change path.size.toNat = 0
      omega
    apply Rank.advances limit source.memory post.memory node child.child position (position + path.size) active
    · rw [addition]
      omega
    · exact nextBounded

theorem Graph.extension_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (node nibs position : BitVec 64) (limit : Nat)
    (key : KeyView source.memory source.memaddrs source.be nibs limit)
    (member : graph.valid node) (active : node ≠ 0#64) (tag : wordAt source.memory node = 2#64)
    (bounded : position.toNat ≤ limit)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsCell : source.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (limitCell : source.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))))
    (code : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one)) :
    source.clock - (evaluateHOLFiniteState source TrieWalk.extension).2.clock ≤ 15 := by
  let path := graph.path node member active (Or.inr tag)
  exact TrieWalk.extension_cost source node nibs position path.size path.pointer limit key.small bounded nodeCell nibsCell posCell limitCell
    path.sizeMapped path.sizeStored path.pointerMapped path.pointerStored path.fits
    (fun within => KeyView.window_fits source.memory source.memaddrs source.be nibs position limit path.size.toNat key bounded within)
    path.mapped
    (fun within => KeyView.window_mapped source.memory source.memaddrs source.be nibs position limit path.size.toNat key bounded within)
    code

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.extension_normal
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.extension_cost
