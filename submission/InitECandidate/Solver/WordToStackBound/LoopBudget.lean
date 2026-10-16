import InitECandidate.Solver.WordToStackBound.Budget
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Loop

namespace InitECandidate.Solver.WordToStackBound.Loop
open Flapjack

 theorem cutFields {width : Nat} [NeZero width] {C F : Type}
    (names : Spt Unit) (source post : WordSemStateFiniteExact width C F)
    (cut : WordSemStateFiniteExact.cutState (names,.ln) source = some post) :
    post.clock = source.clock ∧ post.code = source.code := by
  unfold WordSemStateFiniteExact.cutState at cut
  cases env : wordSemCutEnv (names,.ln) source.locals <;> simp [env] at cut
  next locals => subst post; exact ⟨rfl, rfl⟩

theorem sourceTailClock {width : Nat} [NeZero width] {C F : Type}
    (names exitNames : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (source cutSource bodyPost finalPost : WordSemStateFiniteExact width C F)
    (bodyResult finalResult : Option (WordSemResult width))
    (cut : WordSemStateFiniteExact.cutState (names,.ln) source = some cutSource)
    (bodyRun : WordSemStateFiniteExact.evaluate body cutSource = (bodyResult,bodyPost))
    (loopRun : WordSemStateFiniteExact.evaluate (.loop names body exitNames) source = (finalResult,finalPost)) :
    finalPost.clock ≤ bodyPost.clock := by
  rw [WordSemStateFiniteExact.evaluate,cut] at loopRun
  simp only [] at loopRun
  rw [WordSemStateFiniteExact.fix_clock_evaluate,bodyRun] at loopRun
  by_cases continues : wordSemContLoop bodyResult = true
  · simp only [continues,if_true] at loopRun
    by_cases zero : bodyPost.clock = 0
    · simp only [zero] at loopRun
      obtain ⟨rfl,rfl⟩ := loopRun
      exact Nat.le_refl _
    · simp only [zero] at loopRun
      have bound := (WordSemStateFiniteExact.evaluate_clock
        (wordSemSTOP (.loop names body exitNames)) (WordSemStateFiniteExact.decClock bodyPost)
        finalResult finalPost loopRun).1
      simpa only [WordSemStateFiniteExact.decClock] using bound.trans (Nat.sub_le _ _)
  · simp only [continues] at loopRun
    cases bodyResult with
    | none => simp only [wordSemExitLoop] at loopRun; obtain ⟨rfl,rfl⟩ := loopRun; exact Nat.le_refl _
    | some result =>
      cases result <;> try (simp only [wordSemExitLoop] at loopRun; obtain ⟨rfl,rfl⟩ := loopRun; exact Nat.le_refl _)
      next depth =>
        cases depth with
        | zero =>
          cases exitCut : WordSemStateFiniteExact.cutState (exitNames,.ln) bodyPost with
          | none => simp [exitCut] at loopRun; obtain ⟨rfl,rfl⟩ := loopRun; exact Nat.le_refl _
          | some exitPost =>
            simp only [exitCut] at loopRun
            obtain ⟨rfl,rfl⟩ := loopRun
            exact (cutFields exitNames bodyPost finalPost exitCut).1.le
        | succ depth =>
          simp only [wordSemExitLoop] at loopRun
          obtain ⟨rfl,rfl⟩ := loopRun
          exact Nat.le_refl _

theorem loopBudget (limit initial middle final bodyExtra recursiveExtra bodyCost : Nat)
    (bodyDecrease : middle ≤ initial) (nonzero : middle ≠ 0)
    (recursiveDecrease : final ≤ middle - 1) (costBound : bodyCost ≤ 2 * limit)
    (bodyBound : bodyExtra ≤ (2 * limit) * (initial - middle) + bodyCost)
    (recursiveBound : recursiveExtra ≤ (2 * limit) * ((middle - 1) - final) + bodyCost) :
    bodyExtra + recursiveExtra ≤ (2 * limit) * (initial - final) + bodyCost := by
  have paid := consumeBudget (2 * limit) middle final recursiveExtra bodyCost
    nonzero recursiveDecrease costBound recursiveBound
  simpa only [Nat.add_zero] using composeBudget (2 * limit) initial middle final
    bodyExtra recursiveExtra bodyCost 0 bodyDecrease (by omega) bodyBound
    (by simpa only [Nat.add_zero] using paid)

end InitECandidate.Solver.WordToStackBound.Loop
#print axioms InitECandidate.Solver.WordToStackBound.Loop.cutFields
#print axioms InitECandidate.Solver.WordToStackBound.Loop.sourceTailClock
#print axioms InitECandidate.Solver.WordToStackBound.Loop.loopBudget
