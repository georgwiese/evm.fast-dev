import InitECandidate.Solver.GasBudget.McopyProgram
import InitECandidate.Solver.GasBudget.MemoryCostKnownCalls

namespace InitECandidate.Solver.GasBudget.Mcopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite

def wordFee (len : U256Value.Words) : BitVec 64 := 3#64 + 3#64 * WordsOf.resultWord (SatWord.resultWord len)
def chargeWord (src dst len : U256Value.Words) (current : BitVec 64) : BitVec 64 :=
  SaturatingAdd.resultWord (wordFee len) (MemoryExpansionCost2.resultPair src len dst len current).1

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 10000 in
theorem setup_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current : BitVec 64)
    (src dst len : U256Value.Words) (view : MemoryExpansionCost.View source frame current)
    (srcLocal : source.locals.lookup (ofString "src") = some (U256Value.tuple src))
    (dstLocal : source.locals.lookup (ofString "dst") = some (U256Value.tuple dst))
    (lenLocal : source.locals.lookup (ofString "len") = some (U256Value.tuple len))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source program = (some (.returned returned), post)) :
    ∃ (paid : Nat) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ 48 ∧ paid ≤ source.clock ∧ Input.LocalEffects.erase ready = Input.LocalEffects.erase source ∧
      ready.clock = source.clock - paid ∧
      ready.locals.lookup (ofString "src") = some (U256Value.tuple src) ∧
      ready.locals.lookup (ofString "dst") = some (U256Value.tuple dst) ∧
      ready.locals.lookup (ofString "n") = some (.val (.word (SatWord.resultWord len))) ∧
      ready.locals.lookup (ofString "x") = some (MemoryExpansionCost.pairValue (MemoryExpansionCost2.resultPair src len dst len current)) ∧
      ready.locals.lookup (ofString "cost") = some (.val (.word (chargeWord src dst len current))) ∧
      evaluateHOLFiniteState ready afterFee = (some (.returned returned), inner) ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase inner ∧ post.clock = inner.clock := by
  rw [program] at normal
  have lenRead : eval source (localVar "len") = some (U256Value.tuple len) := by simp [eval, localVar, evalHOLExact, toExact, lenLocal]
  obtain ⟨paidN, first, firstPost, positiveN, boundN, fitsN, firstEq, firstFields, wordsRun, firstScope⟩ :=
    MemoryCostCalls.normal .sat source post "n" (localVar "len") afterSat len returned view.installed lenRead normal
  have firstN := Input.KnownUnaryPrefix.lookup_same firstEq
  have firstOther (key : String) (other : ofString "n" ≠ ofString key) := Input.KnownUnaryPrefix.lookup_other firstEq key other
  have nRead : eval first (localVar "n") = some (.val (.word (SatWord.resultWord len))) := by
    simp [eval, localVar, evalHOLExact, toExact, firstN, MemoryCostCalls.Kind.result]
  obtain ⟨paidW, second, secondPost, positiveW, boundW, fitsW, secondEq, secondFields, costRun, secondScope⟩ :=
    MemoryCostCalls.normal .words first firstPost "w" (localVar "n") afterWords (SatWord.resultWord len) returned
      (MemoryCostCalls.installed_after firstFields view.installed) nRead wordsRun
  have secondOther (key : String) (other : ofString "w" ≠ ofString key) := Input.KnownUnaryPrefix.lookup_other secondEq key other
  have secondSrc := (secondOther "src" (by decide)).trans ((firstOther "src" (by decide)).trans srcLocal)
  have secondDst := (secondOther "dst" (by decide)).trans ((firstOther "dst" (by decide)).trans dstLocal)
  have secondLen := (secondOther "len" (by decide)).trans ((firstOther "len" (by decide)).trans lenLocal)
  have secondN := (secondOther "n" (by decide)).trans firstN
  have secondW := Input.KnownUnaryPrefix.lookup_same secondEq
  have costArgs : evalListHOLFinite second (h := fun address => Classical.propDecidable (second.memaddrs address))
      [localVar "src", localVar "len", localVar "dst", localVar "len"] = some [U256Value.tuple src, U256Value.tuple len, U256Value.tuple dst, U256Value.tuple len] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, secondSrc, secondDst, secondLen]
  obtain ⟨paidX, third, thirdPost, positiveX, boundX, fitsX, thirdEq, thirdFields, addRun, thirdScope⟩ :=
    MemoryExpansionCost2.normal_prefix second secondPost frame current src len dst len (view.after_erase (secondFields.trans firstFields))
      "x" [localVar "src", localVar "len", localVar "dst", localVar "len"] afterCost returned costArgs costRun
  have thirdX := Input.KnownUnaryPrefix.lookup_same thirdEq
  have thirdOther (key : String) (other : ofString "x" ≠ ofString key) := Input.KnownUnaryPrefix.lookup_other thirdEq key other
  have thirdW := (thirdOther "w" (by decide)).trans secondW
  have code := OriginalCodeEnvironment.arithmetic third.code (MemoryCostCalls.installed_after (thirdFields.trans (secondFields.trans firstFields)) view.installed) .add_sat
  rw [ChargeWithMemory.add_signature] at code
  obtain ⟨a, b, inner, funded, actualArgs, lower, tailRun, finalScope⟩ :=
    SaturatingAdd.normal_prefix third thirdPost "cost" [fee, .rfield 0 (localVar "x")] afterFee code returned addRun
  have expectedArgs : evalListHOLFinite third (h := fun address => Classical.propDecidable (third.memaddrs address)) [fee, .rfield 0 (localVar "x")] =
      some [.val (.word (wordFee len)), .val (.word (MemoryExpansionCost2.resultPair src len dst len current).1)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, fee, wordFee, localVar, thirdW, thirdX,
      MemoryCostCalls.Kind.result, MemoryExpansionCost.pairValue, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL]
  have valuesEq := Option.some.inj (actualArgs.symm.trans expectedArgs)
  have identified : a = wordFee len ∧ b = (MemoryExpansionCost2.resultPair src len dst len current).1 := by simpa using valuesEq
  obtain ⟨aEq, bEq⟩ := identified
  subst a
  subst b
  let ready := bind {third with clock := third.clock - 1} "cost" (chargeWord src dst len current)
  have firstClock : first.clock = source.clock - paidN := by rw [firstEq]; rfl
  have secondClock : second.clock = first.clock - paidW := by rw [secondEq]; rfl
  have thirdClock : third.clock = second.clock - paidX := by rw [thirdEq]; rfl
  have other (key : String) (different : ofString "cost" ≠ ofString key) : ready.locals.lookup (ofString key) = third.locals.lookup (ofString key) := bind_lookup_other _ "cost" key _ different
  refine ⟨paidN + paidW + paidX + 1, ready, inner, by change paidN ≤ 1 at boundN; change paidW ≤ 3 at boundW; omega, ?_,
    thirdFields.trans (secondFields.trans firstFields), ?_, ?_, ?_, ?_, ?_, bind_lookup_same _ _ _, tailRun, ?_, ?_⟩
  · rw [thirdClock, secondClock, firstClock] at funded
    rw [secondClock, firstClock] at fitsX
    rw [firstClock] at fitsW
    omega
  · change third.clock - 1 = _
    rw [thirdClock, secondClock, firstClock]
    omega
  · exact (other "src" (by decide)).trans ((thirdOther "src" (by decide)).trans secondSrc)
  · exact (other "dst" (by decide)).trans ((thirdOther "dst" (by decide)).trans secondDst)
  · exact (other "n" (by decide)).trans ((thirdOther "n" (by decide)).trans secondN)
  · exact (other "x" (by decide)).trans thirdX
  · rw [firstScope, secondScope, thirdScope, finalScope]; rfl
  · rw [firstScope, secondScope, thirdScope, finalScope]; rfl

end InitECandidate.Solver.GasBudget.Mcopy

#print axioms InitECandidate.Solver.GasBudget.Mcopy.setup_value
