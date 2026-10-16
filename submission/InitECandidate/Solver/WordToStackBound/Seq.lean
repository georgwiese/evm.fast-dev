import InitECandidate.Solver.WordToStackBound.Budget

namespace InitECandidate.Solver.WordToStackBound.Seq
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect

theorem compCorrectSeqFirstNonNone {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (first second : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : (∀ result middle,
      (result, middle) = WordSemStateFiniteExact.evaluate first source ∧ result = none →
        Simulation ac limit second middle) ∧ Simulation ac limit first source)
    (firstNonNone : (WordSemStateFiniteExact.evaluate first source).1 ≠ none) :
    Simulation ac limit (.seq first second) source := by
  intro safe supported bounded k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  have supportedParts := seqSupported supported
  have costParts := seqCeiling first second limit bounded
  rcases premises with ⟨execution, notError, related, conventions, flat,
    compilation, lengthBound, bitmapBound, bitmapPrefix, labels, maxBound⟩
  rcases firstCompile : compNative ac false first (bs, n) (k, f, frame) with
    ⟨firstCode, middleBitmaps⟩
  rcases secondCompile : compNative ac false second middleBitmaps (k, f, frame) with
    ⟨secondCode, finalBitmaps⟩
  simp only [compNative, firstCompile, secondCompile] at compilation
  obtain ⟨compiledEq, bitmapEq⟩ := Prod.mk.inj compilation
  subst compiled
  have firstPrefix := compImpIsPrefix ac false second middleBitmaps (k, f, frame)
    secondCode finalBitmaps secondCompile
  rw [bitmapEq] at firstPrefix
  have firstLabels : ∀ loc, StackSem.getLabelsExact firstCode loc →
      StackSem.locCheckExact target.code loc := by
    intro loc member
    apply labels loc
    rw [StackSem.getLabelsExact]
    exact Or.inl member
  have firstConventions : postAllocConventionsHOL k first = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL,
      callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    exact ⟨conventions.1.1, conventions.2.1.1, conventions.2.2.1⟩
  have firstFlat : flatExpConventions first = true := by
    simp only [flatExpConventions, Bool.and_eq_true] at flat
    exact flat.1
  have firstMax : maxVarHOL first < 2 * frame + 2 * k := by
    simp only [maxVarHOL] at maxBound
    omega
  rw [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate] at execution
  rcases firstRun : WordSemStateFiniteExact.evaluate first source with ⟨firstResult, middle⟩
  rw [firstRun] at firstNonNone execution
  cases firstResult with
  | none => exact False.elim (firstNonNone rfl)
  | some value =>
    obtain ⟨resultEq, sourceEq⟩ := Prod.mk.inj execution
    subst result
    subst sourcePost
    obtain ⟨clock, targetPost, targetResult, budget, targetRun, conclusion⟩ :=
      ih.2 safe supportedParts.1 costParts.1 k f frame middle target (some value) bs middleBitmaps.1 n middleBitmaps.2
        firstCode lens ⟨firstRun, notError, related, firstConventions, firstFlat,
          firstCompile, lengthBound, bitmapBound, firstPrefix.trans bitmapPrefix,
          firstLabels, firstMax⟩
    have targetNonNone : targetResult ≠ none := by
      intro eq
      subst targetResult
      simp [compCorrectResult] at conclusion
    refine ⟨clock, targetPost, targetResult, by simp only [cost]; omega, ?_, conclusion⟩
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, targetRun]
    cases targetResult with
    | none => exact False.elim (targetNonNone rfl)
    | some output => rfl


-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectSeqFirstNone {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (first second : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : (∀ result middle,
      (result, middle) = WordSemStateFiniteExact.evaluate first source ∧ result = none →
        Simulation ac limit second middle) ∧ Simulation ac limit first source)
    (firstNone : (WordSemStateFiniteExact.evaluate first source).1 = none) :
    Simulation ac limit (.seq first second) source := by
  classical
  intro safe supported bounded k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  have supportedParts := seqSupported supported
  have costParts := seqCeiling first second limit bounded
  rcases premises with ⟨execution, notError, related, conventions, flat,
    compilation, lengthBound, bitmapBound, bitmapPrefix, labels, maxBound⟩
  rcases firstCompile : compNative ac false first (bs, n) (k, f, frame) with
    ⟨firstCode, middleBitmaps⟩
  rcases secondCompile : compNative ac false second middleBitmaps (k, f, frame) with
    ⟨secondCode, finalBitmaps⟩
  simp only [compNative, firstCompile, secondCompile] at compilation
  obtain ⟨compiledEq, bitmapEq⟩ := Prod.mk.inj compilation
  subst compiled
  have firstPrefix := compImpIsPrefix ac false second middleBitmaps (k, f, frame)
    secondCode finalBitmaps secondCompile
  rw [bitmapEq] at firstPrefix
  have firstLabels : ∀ loc, StackSem.getLabelsExact firstCode loc →
      StackSem.locCheckExact target.code loc := by
    intro loc member
    apply labels loc
    rw [StackSem.getLabelsExact]
    exact Or.inl member
  have firstConventions : postAllocConventionsHOL k first = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL,
      callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    exact ⟨conventions.1.1, conventions.2.1.1, conventions.2.2.1⟩
  have firstFlat : flatExpConventions first = true := by
    simp only [flatExpConventions, Bool.and_eq_true] at flat
    exact flat.1
  have firstMax : maxVarHOL first < 2 * frame + 2 * k := by
    simp only [maxVarHOL] at maxBound
    omega
  have secondConventions : postAllocConventionsHOL k second = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL,
      callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    exact ⟨conventions.1.2, conventions.2.1.2, conventions.2.2.2⟩
  have secondFlat : flatExpConventions second = true := by
    simp only [flatExpConventions, Bool.and_eq_true] at flat
    exact flat.2
  have secondMax : maxVarHOL second < 2 * frame + 2 * k := by
    simp only [maxVarHOL] at maxBound
    omega
  rw [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate] at execution
  rcases firstRun : WordSemStateFiniteExact.evaluate first source with ⟨firstResult, middle⟩
  rw [firstRun] at firstNone execution
  cases firstResult with
  | some value => cases firstNone
  | none =>
    obtain ⟨clock, targetMiddle, firstTargetResult, budget, targetRun, firstConclusion⟩ :=
      ih.2 safe supportedParts.1 costParts.1 k f frame middle target none bs middleBitmaps.1 n middleBitmaps.2
        firstCode lens ⟨firstRun, by simp, related, firstConventions, firstFlat,
          firstCompile, lengthBound, bitmapBound, firstPrefix.trans bitmapPrefix,
          firstLabels, firstMax⟩
    have firstDecrease := (WordSemStateFiniteExact.evaluate_clock first source none middle firstRun).1
    have secondDecrease := (WordSemStateFiniteExact.evaluate_clock second middle result sourcePost execution).1
    cases firstTargetResult with
    | some value =>
      simp [compCorrectResult] at firstConclusion
      rcases firstConclusion with ⟨valueEq, events, resource⟩
      subst value
      have finalEvents := WordSemStateFiniteExact.evaluate_io_events_mono
        second middle result sourcePost execution
      have resourceThe : miscThe (middle.stackLimit + 1) middle.stackMax > middle.stackLimit := by
        cases h : middle.stackMax <;> simp_all [miscThe]
      have finalResourceThe := WordSemStateFiniteExact.evaluate_stack_limit_stack_max
        second middle result sourcePost ⟨execution, resourceThe⟩
      have finalResource : sourcePost.stackMax.getD (sourcePost.stackLimit + 1) >
          sourcePost.stackLimit := by
        cases h : sourcePost.stackMax <;> simp_all [miscThe]
      have dimension : goodDimindex width := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have mismatch : result.map compileResult ≠ some (.halt (.word 2)) := by
        cases result with
        | none => simp
        | some value =>
          simp only [Option.map_some, ne_eq, Option.some.injEq]
          exact Ne.symm ((haltEqCompileResult value).2 dimension)
      refine ⟨clock, targetMiddle, some (.halt (.word 2)),
        extendBudget (2 * limit) source.clock middle.clock sourcePost.clock clock
          (cost first) (cost second) secondDecrease budget, ?_, ?_⟩
      · rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, targetRun]
        rfl
      · unfold compCorrectResult
        split
        · exact ⟨rfl, events.trans finalEvents, finalResource⟩
        · rename_i equal
          exact False.elim (mismatch (by simpa using equal))
    | none =>
      simp only [compCorrectResult, Option.map_none, ne_eq, not_true_eq_false,
        ↓reduceIte] at firstConclusion
      have accounting := compImpLength ac false first (bs, n) (k, f, frame)
        firstCode middleBitmaps ⟨firstCompile, lengthBound⟩
      have mono := Flapjack.Compiler.Backend.StackProps.EvaluateMono.evaluateMono
        firstCode {target with clock := target.clock + clock} targetMiddle none targetRun
      have gap := accounting.2
      have secondBitmapBound : middleBitmaps.2 - (appListAppend middleBitmaps.1).length ≤
          targetMiddle.bitmaps.length := by
        rw [← gap]
        exact bitmapBound.trans mono.1.length_le
      have secondPrefix : (appListAppend finalBitmaps.1).IsPrefix
          (targetMiddle.bitmaps.drop
            (middleBitmaps.2 - (appListAppend middleBitmaps.1).length)) := by
        rw [← gap, bitmapEq]
        exact bitmapPrefix.trans (mono.1.drop _)
      have secondLabels : ∀ loc, StackSem.getLabelsExact secondCode loc →
          StackSem.locCheckExact targetMiddle.code loc := by
        intro loc member
        apply LocationLabels.locCheckSubset target.code targetMiddle.code mono.2 loc
        apply labels loc
        rw [StackSem.getLabelsExact]
        exact Or.inr member
      obtain ⟨secondClock, targetPost, targetResult, secondBudget, secondRun, conclusion⟩ :=
        ih.1 none middle ⟨firstRun.symm, rfl⟩ (codeSafe_evaluate safe supportedParts.1 firstRun)
          supportedParts.2 costParts.2 k f frame sourcePost targetMiddle
          result middleBitmaps.1 finalBitmaps.1 middleBitmaps.2 finalBitmaps.2
          secondCode lens ⟨execution, notError, firstConclusion, secondConventions,
            secondFlat, secondCompile, accounting.1, secondBitmapBound, secondPrefix,
            secondLabels, secondMax⟩
      have extendedFirst := Flapjack.Compiler.Backend.StackProps.evaluateAddClock
        secondClock firstCode {target with clock := target.clock + clock}
        none targetMiddle ⟨targetRun, by simp⟩
      have handlerEq : middle.handler = source.handler := by
        have preserved := WordSemStackEq.evaluateStackSwap first source
        unfold WordSemStackEq.stackSwapPost at preserved
        rw [firstRun] at preserved
        exact preserved.2.1
      have finalConclusion : compCorrectResult ac k f frame source sourcePost
          targetPost result targetResult lens := by
        unfold compCorrectResult at conclusion ⊢
        rw [handlerEq] at conclusion
        exact conclusion
      refine ⟨clock + secondClock, targetPost, targetResult,
        composeBudget (2 * limit) source.clock middle.clock sourcePost.clock clock secondClock
          (cost first) (cost second) firstDecrease secondDecrease budget secondBudget,
        ?_, finalConclusion⟩
      rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
      have clockEq : {target with clock := target.clock + (clock + secondClock)} =
          {{target with clock := target.clock + clock} with
            clock := (target.clock + clock) + secondClock} := by
        simp only [Nat.add_assoc]
      rw [clockEq, extendedFirst]
      exact secondRun


-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectSeq {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (first second : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : (∀ result middle,
      (result, middle) = WordSemStateFiniteExact.evaluate first source ∧ result = none →
        Simulation ac limit second middle) ∧ Simulation ac limit first source) :
    Simulation ac limit (.seq first second) source := by
  by_cases guard : (WordSemStateFiniteExact.evaluate first source).1 = none
  · exact compCorrectSeqFirstNone ac limit first second source ih guard
  · exact compCorrectSeqFirstNonNone ac limit first second source ih guard

end InitECandidate.Solver.WordToStackBound.Seq
#print axioms InitECandidate.Solver.WordToStackBound.Seq.compCorrectSeq
