import InitECandidate.Solver.WordToStackBound.CallBudget
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturning

namespace InitECandidate.Solver.WordToStackBound.CallReturning
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning

def InductionHypotheses {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) : Prop :=
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (location : WordLocW width) (ys : List (WordLocW width))
    (calleePost popped : WordSemStateFiniteExact width (Nat × C) F),
    SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 ∧
    WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none
          (WordSemStateFiniteExact.decClock source))) =
      (some (.result location ys), calleePost) ∧
    ¬ (location ≠ .loc l1 l2 ∨ ys.length ≠ values.length) ∧
    WordSemStateFiniteExact.popEnv calleePost = some popped ∧
    sptDomainEqUnion popped.locals envs.1 envs.2 →
    Simulation ac limit retCode (WordSemStateFiniteExact.setVars values ys popped)) ∧
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width)),
    SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 →
    Simulation ac limit prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none
          (WordSemStateFiniteExact.decClock source))))

theorem simulateCalleeBodyAt {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (k callerSize callerFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (destinationCode : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source saved lens 0)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * callerFrame + 2 * k)
    (destinationCompile : callDestNative dest args (k, callerSize, callerFrame) =
      (destinationCode, destination))
    (ih : InductionHypotheses ac limit values names retCode l1 l2 dest args source)
    (safe : CodeSafe limit source.code)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (location calleeSize calleeFrame : Nat) (body : HolProg width)
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (targetCode : sptLookup location saved.code = some
      (.seq (.stackAlloc (calleeSize - (args1.length - k))) body))
    (bodyCompile : compNative ac false prog (bs, n) (k, calleeSize, calleeFrame) =
      (body, (bsPost, nPost)))
    (bodyConventions : postAllocConventionsHOL k prog = true)
    (bodyFlat : flatExpConventions prog = true)
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ saved.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix
      (saved.bitmaps.drop (n - (appListAppend bs).length)))
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (calleeShape : if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1)
    (argumentBound : args1.length - k ≤ calleeFrame)
    (bodyMaximum : maxVarHOL prog < 2 * calleeFrame + 2 * k)
    (space : calleeSize ≤ saved.stackSpace) :
    ∃ (moved entry : StackSemStateFiniteExact width C F)
          (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
          (targetResult : Option (StackSemResult width)),
          extraClock ≤ (2 * limit) * ((source.clock - 1) - bodyPost.clock) + cost prog ∧
          StackSemEvaluate.evaluate (stackArgsNative destination (args.length + 1)
            (k, callerSize, callerFrame), saved) = (none, moved) ∧
          StackSemEvaluate.evaluate
            (.stackAlloc (calleeSize - (args1.length - k)),
              StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
            (none, entry) ∧
          StackSemEvaluate.evaluate (body, {entry with clock := entry.clock + extraClock}) =
            (targetResult, targetPost) ∧
          StackSemEvaluate.evaluate
            (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
              {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
                clock := (StackSemStateOps.decClock moved).clock + extraClock}) =
            (targetResult, targetPost) ∧
          compCorrectResult ac k calleeSize calleeFrame
            (WordSemStateFiniteExact.callEnv args1 ss
              (WordSemStateFiniteExact.pushEnv envs none
                (WordSemStateFiniteExact.decClock source)))
            bodyPost targetPost bodyResult targetResult (callerFrame :: lens) := by
  obtain ⟨moved, entry, moveRun, allocationRun, entryRelation⟩ :=
    enterCallee ac k callerSize callerFrame calleeSize calleeFrame values names retCode
      l1 l2 dest args source saved lens xs args1 prog ss envs destinationCode destination
      guards callerRelation pushedRelation conventions maximum destinationCompile
      calleeShape calleeLocalsSize argumentBound space
  have moveGrowth := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (stackArgsNative destination (args.length + 1) (k, callerSize, callerFrame))
    saved moved none moveRun
  have entryGrowth := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (.stackAlloc (calleeSize - (args1.length - k)))
    (StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved))
    entry none allocationRun
  have bitmapGrowth : saved.bitmaps.IsPrefix entry.bitmaps :=
    moveGrowth.1.trans entryGrowth.1
  have codeGrowth : sptSubspt saved.code entry.code :=
    sptSubsptTrans _ _ _ ⟨moveGrowth.2, entryGrowth.2⟩
  have labels : ∀ loc, StackSem.getLabelsExact body loc →
      StackSem.locCheckExact entry.code loc := by
    intro loc member
    apply LocationLabels.locCheckSubset saved.code entry.code codeGrowth loc
    exact Or.inr ⟨location, .seq (.stackAlloc (calleeSize - (args1.length - k))) body,
      targetCode, by unfold StackSem.getLabelsExact; exact Or.inr member⟩
  have bodyNotError := calleeNotError values names retCode l1 l2 dest args source
    sourcePost bodyPost result bodyResult xs args1 prog ss envs guards nonzero execution
    notError bodyRun
  have bodySafe := codeSafe_findCode safe guards.2.2.1
  obtain ⟨extraClock, targetPost, targetResult, budget, targetRun, conclusion⟩ :=
    ih.2 xs args1 prog ss envs ⟨guards, nonzero⟩
      (by simpa only [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
        WordSemStateFiniteExact.decClock] using safe) bodySafe.1 bodySafe.2 k calleeSize calleeFrame bodyPost entry
      bodyResult bs bsPost n nPost body (callerFrame :: lens)
      ⟨bodyRun, bodyNotError, entryRelation, bodyConventions, bodyFlat, bodyCompile,
        bitmapLength, bitmapBound.trans bitmapGrowth.length_le,
        bitmapPrefix.trans (bitmapGrowth.drop _), labels, bodyMaximum⟩
  have allocationClock : ∀ extra : Nat,
      StackSemEvaluate.evaluate
        (.stackAlloc (calleeSize - (args1.length - k)),
          {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
            clock := (StackSemStateOps.decClock moved).clock + extra}) =
        (none, {entry with clock := entry.clock + extra}) := by
    intro extra
    have success := allocationRun
    rw [StackSemEvaluate.evaluate_stackAlloc] at success
    split_ifs at success with disabled insufficient
    · cases (Prod.mk.inj success).1
    · cases (Prod.mk.inj success).1
    obtain ⟨_, rfl⟩ := Prod.mk.inj success
    rw [StackSemEvaluate.evaluate_stackAlloc, if_neg disabled, if_neg insufficient]
    rfl
  have calleeRun : StackSemEvaluate.evaluate
      (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
        {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
          clock := (StackSemStateOps.decClock moved).clock + extraClock}) =
      (targetResult, targetPost) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
      allocationClock extraClock]
    exact targetRun
  exact ⟨moved, entry, extraClock, targetPost, targetResult,
    by simpa only [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
      WordSemStateFiniteExact.decClock] using budget, moveRun, allocationRun,
    targetRun, calleeRun, conclusion⟩

theorem executeReturningContinuation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (k f frame : Nat) (values : List Nat)
    (retCode : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target restored : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (ih : Simulation ac limit retCode source)
    (safe : CodeSafe limit source.code)
    (supported : noInstallSubprogsHOL retCode = true)
    (bounded : ceiling retCode ≤ limit)
    (sourceRun : WordSemStateFiniteExact.evaluate retCode source = (result, sourcePost))
    (notError : result ≠ some .error)
    (related : stateRel ac k f frame source restored lens 0)
    (conventions : postAllocConventionsHOL k retCode = true)
    (flat : flatExpConventions retCode = true)
    (compilation : compNative ac false retCode (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ restored.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix
      (restored.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact restored.code loc)
    (maximum : maxVarHOL retCode < 2 * frame + 2 * k)
    (copyRun : StackSemEvaluate.evaluate
      (copyRetNative false false (k, f, frame) values .skip, target) = (none, restored)) :
    ∃ (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      extraClock ≤ (2 * limit) * (source.clock - sourcePost.clock) + cost retCode ∧
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, f, frame) values compiled,
          {target with clock := target.clock + extraClock}) = (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  obtain ⟨extraClock, targetPost, targetResult, budget, continuationRun, conclusion⟩ :=
    ih safe supported bounded k f frame sourcePost restored result bs bsPost n nPost compiled lens
      ⟨sourceRun, notError, related, conventions, flat, compilation, lengthBound,
        bitmapBound, bitmapPrefix, labels, maximum⟩
  have clockFree := returnCopyClockFree (width := width) (C := C) (F := F) k f frame values
  have sameClock := clockFree target target.clock
  rw [show {target with clock := target.clock} = target from rfl, copyRun] at sameClock
  simp only [Prod.map, id_eq, Prod.mk.injEq] at sameClock
  have clockEq : restored.clock = target.clock := by
    have projected := congrArg
      (fun state : StackSemStateFiniteExact width C F => state.clock) sameClock.2
    exact projected
  have clockedCopy := clockFree target (target.clock + extraClock)
  rw [copyRun] at clockedCopy
  simp only [Prod.map, id_eq] at clockedCopy
  have outputClock : {restored with clock := target.clock + extraClock} =
      {restored with clock := restored.clock + extraClock} := by rw [clockEq]
  rw [outputClock] at clockedCopy
  refine ⟨extraClock, targetPost, targetResult, budget, ?_, conclusion⟩
  rw [CallReturnEval.evaluateCopyRetSeq, StackSemEvaluate.evaluate_seq,
    StackSemEvaluateClock.fixClockEvaluate, clockedCopy]
  simp only
  exact continuationRun

end InitECandidate.Solver.WordToStackBound.CallReturning
#print axioms InitECandidate.Solver.WordToStackBound.CallReturning.simulateCalleeBodyAt
#print axioms InitECandidate.Solver.WordToStackBound.CallReturning.executeReturningContinuation
