import InitECandidate.Solver.Mpt.TrieWalkExtensionCompare
import InitECandidate.Solver.Mpt.TrieWalkRead

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

/-- A real continuing original extension derives its child, bounded
position, paid comparison and exact restored caller from current physical
node/key facts. Only the potentially visited prefix of a path is required. -/
theorem extension_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node nibs position size path child : BitVec 64) (limit : Nat)
    (small : limit ≤ 64) (bounded : position.toNat ≤ limit)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (nibsCell : source.locals.lookup (ofString "nibs") = some (.val (.word nibs)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (limitCell : source.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))))
    (sizeMapped : source.memaddrs (node + 40#64)) (sizeStored : source.memory (node + 40#64) = .word size)
    (pathMapped : source.memaddrs (node + 32#64)) (pathStored : source.memory (node + 32#64) = .word path)
    (childMapped : source.memaddrs (node + 48#64)) (childStored : source.memory (node + 48#64) = .word child)
    (aFits : path.toNat + min size.toNat 64 < 2^64)
    (bFits : size.toNat ≤ limit - position.toNat → (nibs + position).toNat + size.toNat < 2^64)
    (leftMapped : ∀ offset < min size.toNat 64, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress path offset)))
    (rightMapped : size.toNat ≤ limit - position.toNat →
      ∀ offset < size.toNat, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress (nibs + position) offset)))
    (code : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (normal : evaluateHOLFiniteState source extension = (none, post)) :
    ∃ paid, 1 ≤ paid ∧ paid ≤ MemeqByteRuntime.price size.toNat + 1 ∧ paid ≤ source.clock ∧
      size.toNat ≤ limit - position.toNat ∧
      (position + size).toNat = position.toNat + size.toNat ∧ (position + size).toNat ≤ limit ∧
      post = bind (bind {source with clock := source.clock - paid} "pos" (position + size)) "node" child := by
  have sizeRead := node_field_read source node 40#64 size nodeCell sizeMapped sizeStored
  rw [extension_shape] at normal
  obtain ⟨inner, tailRun, scope⟩ := Input.declaration_none source post "sl" (nodeField 40#64) size _ sizeRead normal
  let entered := bind source "sl" size
  change evaluateHOLFiniteState entered (.seq extentGuard extensionCompare) = (none, inner) at tailRun
  have currentNode : entered.locals.lookup (ofString "node") = some (.val (.word node)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans nodeCell
  have currentNibs : entered.locals.lookup (ofString "nibs") = some (.val (.word nibs)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans nibsCell
  have currentPos : entered.locals.lookup (ofString "pos") = some (.val (.word position)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans posCell
  have currentLimit : entered.locals.lookup (ofString "nlen") = some (.val (.word (BitVec.ofNat 64 limit))) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans limitCell
  have currentSize : entered.locals.lookup (ofString "sl") = some (.val (.word size)) := bind_lookup_same _ _ _
  obtain ⟨passed, guardRun, compareRun⟩ := Input.sequence_none entered inner extentGuard extensionCompare tailRun
  obtain ⟨within, sizeSmall, addition, nextBounded, passedEq⟩ :=
    extent_guard_numeral entered passed position size limit small bounded currentPos currentLimit currentSize guardRun
  subst passed
  have clipped : min size.toNat 64 = size.toNat := min_eq_left sizeSmall
  rw [clipped] at aFits leftMapped
  have bFits := bFits within
  have rightMapped := rightMapped within
  have args := compare_arguments_read entered node nibs position size path currentNode currentNibs currentPos currentSize pathMapped pathStored
  obtain ⟨paid, nextNode, positive, cost, funded, childRead, innerEq⟩ :=
    extension_compare_normal entered inner node position size path (nibs + position) currentNode currentPos currentSize
      sizeSmall aFits bFits leftMapped rightMapped code args compareRun
  let positioned := bind (compared entered paid) "pos" (position + size)
  change eval positioned (nodeField 48#64) = some (.val (.word nextNode)) at childRead
  have positionedNode : positioned.locals.lookup (ofString "node") = some (.val (.word node)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans
      ((bind_lookup_other _ _ _ _ (by decide)).trans currentNode)
  have observedChild := node_field_read positioned node 48#64 child positionedNode childMapped childStored
  have nextEq : nextNode = child := by
    have same := childRead.symm.trans observedChild
    simpa only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] using same
  subst nextNode
  refine ⟨paid, positive, cost, funded, within, addition, nextBounded, ?_⟩
  rw [scope, innerEq, restore_bind_other _ _ "sl" "node" _ (by decide),
    restore_bind_other _ _ "sl" "pos" _ (by decide)]
  have back : restore source "sl" {entered with clock := entered.clock - paid} = {source with clock := source.clock - paid} :=
    restore_bound {source with clock := source.clock - paid} "sl" size
  rw [back]

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.extension_normal
