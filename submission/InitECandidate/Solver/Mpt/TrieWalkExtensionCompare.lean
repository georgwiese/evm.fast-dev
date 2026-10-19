import InitECandidate.Solver.Mpt.TrieWalkExtensionStep
import InitECandidate.Solver.MutableTable.MemeqSmallNonePrefix
import InitECandidate.Solver.MutableTable.MemeqSmallCallCost
import InitECandidate.Solver.WitnessRadix.Bindings

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

def compared (source : PanSemStateFiniteExact 64 Guest.HostMemory) (paid : Nat) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  bind {source with clock := source.clock - paid} "eq2" 1#64

set_option maxRecDepth 10000 in
theorem after_compare_quiet (code) : Input.QuietClock.Preserves code afterCompare := by
  rw [after_compare_shape, comparison_guard_shape, extension_advance_shape]
  apply Input.QuietClock.sequence
  · exact Input.QuietClock.conditional code _ _ _ (Input.QuietClock.returned code _) (Input.QuietClock.skip code)
  · exact Input.QuietClock.sequence code _ _ (Input.QuietClock.assign code _ _) (Input.QuietClock.assign code _ _)

/-- The actual comparison continuation rejects zero, so a continuing
extension has observed the real original memeq answer one. Its exact caller
state retains the caller's comparison local after leaving that scope. -/
theorem extension_compare_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node position size a b : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node") = some (.val (.word node)))
    (posCell : source.locals.lookup (ofString "pos") = some (.val (.word position)))
    (sizeCell : source.locals.lookup (ofString "sl") = some (.val (.word size)))
    (small : size.toNat ≤ 64) (aFits : a.toNat + size.toNat < 2^64) (bFits : b.toNat + size.toNat < 2^64)
    (leftMapped : ∀ offset < size.toNat, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress a offset)))
    (rightMapped : ∀ offset < size.toNat, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress b offset)))
    (code : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) compareArguments =
      some (MemeqByteRuntime.values a b size.toNat))
    (normal : evaluateHOLFiniteState source extensionCompare = (none, post)) :
    ∃ paid nextNode, 1 ≤ paid ∧ paid ≤ MemeqByteRuntime.price size.toNat + 1 ∧ paid ≤ source.clock ∧
      eval (bind (compared source paid) "pos" (position + size)) (nodeField 48#64) = some (.val (.word nextNode)) ∧
      post = bind (bind {source with clock := source.clock - paid} "pos" (position + size)) "node" nextNode := by
  rw [compare_shape] at normal
  obtain ⟨paid, answer, inner, positive, bounded, funded, binary, tailRun, scope⟩ :=
    MutableTable.MemeqSmall.none_prefix source post a b size.toNat small aFits bFits leftMapped rightMapped
      code "eq2" compareArguments afterCompare args normal
  let resumed := bind {source with clock := source.clock - paid} "eq2" answer
  change evaluateHOLFiniteState resumed afterCompare = (none, inner) at tailRun
  rw [after_compare_shape] at tailRun
  obtain ⟨passed, guardRun, advanceRun⟩ := Input.sequence_none resumed inner comparisonGuard extensionAdvance tailRun
  have answerCell : resumed.locals.lookup (ofString "eq2") = some (.val (.word answer)) := bind_lookup_same _ _ _
  obtain ⟨nonzero, passedEq⟩ := comparison_guard_normal resumed passed answer answerCell guardRun
  subst passed
  have answerOne : answer = 1#64 := by
    rcases binary with zero | one
    · exact (nonzero zero).elim
    · exact one
  have currentNode : resumed.locals.lookup (ofString "node") = some (.val (.word node)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans nodeCell
  have currentPos : resumed.locals.lookup (ofString "pos") = some (.val (.word position)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans posCell
  have currentSize : resumed.locals.lookup (ofString "sl") = some (.val (.word size)) :=
    (bind_lookup_other _ _ _ _ (by decide)).trans sizeCell
  obtain ⟨nextNode, childRead, innerEq⟩ := extension_advance_normal resumed inner node position size currentNode currentPos currentSize advanceRun
  refine ⟨paid, nextNode, positive, bounded, funded, ?_, ?_⟩
  · simpa only [resumed, answerOne, compared] using childRead
  · rw [scope, innerEq, restore_bind_other _ _ "eq2" "node" _ (by decide),
      restore_bind_other _ _ "eq2" "pos" _ (by decide)]
    have back : restore source "eq2" resumed = {source with clock := source.clock - paid} :=
      restore_bound {source with clock := source.clock - paid} "eq2" answer
    rw [back]

theorem extension_compare_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (a b : BitVec 64) (length : Nat)
    (small : length ≤ 64) (aFits : a.toNat + length < 2^64) (bFits : b.toNat + length < 2^64)
    (leftMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress a offset)))
    (rightMapped : ∀ offset < length, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress b offset)))
    (code : source.code.lookup (ofString "memeq") = some (Memeq32.formals, Memeq32.body, .one))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) compareArguments =
      some (MemeqByteRuntime.values a b length)) :
    source.clock - (evaluateHOLFiniteState source extensionCompare).2.clock ≤ MemeqByteRuntime.price length + 1 := by
  rw [compare_shape]
  exact MutableTable.MemeqSmall.call_cost source a b length small aFits bFits leftMapped rightMapped code
    (ofString "eq2") compareArguments afterCompare args (Input.ClockCost.of_quiet _ _ (after_compare_quiet _))

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.after_compare_quiet
#print axioms InitECandidate.Solver.Mpt.TrieWalk.extension_compare_normal
#print axioms InitECandidate.Solver.Mpt.TrieWalk.extension_compare_cost
