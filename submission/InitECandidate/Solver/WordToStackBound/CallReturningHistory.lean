import InitECandidate.Solver.WordToStackBound.CallReturning
import InitECandidate.Solver.WordToStackBound.CallState

namespace InitECandidate.Solver.WordToStackBound.CallReturning
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning

theorem sourceReturningContinuation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (ih : InductionHypotheses ac limit values names retCode l1 l2 dest args source)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost)) :
    ∃ (gc : List (Nat × WordLocW width)) (tail : List (WordSemStackFrame width))
      (popped : WordSemStateFiniteExact width (Nat × C) F),
      bodyPost.stack = .stackFrame source.localsSize (sptToAList envs.1) gc none :: tail ∧
      ((wordSemEnvToList envs.2 source.permute).1).map Prod.fst = gc.map Prod.fst ∧
      WordSemStackEq.sKeyEq source.stack tail ∧ bodyPost.handler = source.handler ∧
      popped = {bodyPost with
        locals := sptUnion (sptFromAList gc) (sptFromAList (sptToAList envs.1)),
        stack := tail, localsSize := source.localsSize} ∧
      WordSemStateFiniteExact.popEnv bodyPost = some popped ∧
      sptDomainEqUnion popped.locals envs.1 envs.2 ∧
      ¬ (location ≠ .loc l1 l2 ∨ returned.length ≠ values.length) ∧
      WordSemStateFiniteExact.evaluate retCode (WordSemStateFiniteExact.setVars values returned popped) =
        (result, sourcePost) ∧
      Simulation ac limit retCode (WordSemStateFiniteExact.setVars values returned popped) := by
  obtain ⟨gc, tail, frame, gcKeys, tailKeys, handler, popRun, domain⟩ :=
    returnedCallerFrame prog source bodyPost envs args1 ss location returned bodyRun
  let popped : WordSemStateFiniteExact width (Nat × C) F := {bodyPost with
    locals := sptUnion (sptFromAList gc) (sptFromAList (sptToAList envs.1)),
    stack := tail, localsSize := source.localsSize}
  have originalGuards := guards
  obtain ⟨get, bad, find, valid, cut⟩ := originalGuards
  rw [WordSemStateFiniteExact.evaluate] at execution
  simp only [get, bad, Bool.false_eq_true, if_false, find, valid, cut] at execution
  rw [dif_neg nonzero, WordSemStateFiniteExact.fix_clock_evaluate, bodyRun] at execution
  simp only at execution
  by_cases invalid : location ≠ .loc l1 l2 ∨ returned.length ≠ values.length
  · rw [if_pos invalid] at execution
    exact False.elim (notError (Prod.mk.inj execution).1.symm)
  rw [if_neg invalid, popRun] at execution
  simp only at execution
  rw [if_pos domain] at execution
  refine ⟨gc, tail, popped, frame, gcKeys, tailKeys, handler, rfl, popRun, domain,
    invalid, execution, ?_⟩
  exact ih.1 xs args1 prog ss envs location returned bodyPost popped
    ⟨guards, nonzero, bodyRun, invalid, popRun, domain⟩

theorem restoreCallerFromBodyReturn {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (k callerSize frame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (saved target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize frame source saved lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (ih : InductionHypotheses ac limit values names retCode l1 l2 dest args source)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost target (some (.result location returned)) (some (.result location)) (frame :: lens)) :
    ∃ (popped : WordSemStateFiniteExact width (Nat × C) F)
      (restored : StackSemStateFiniteExact width C F),
      WordSemStateFiniteExact.popEnv bodyPost = some popped ∧
      WordSemStateFiniteExact.evaluate retCode (WordSemStateFiniteExact.setVars values returned popped) =
        (result, sourcePost) ∧
      Simulation ac limit retCode (WordSemStateFiniteExact.setVars values returned popped) ∧
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, callerSize, frame) values .skip, target) = (none, restored) ∧
      stateRel ac k callerSize frame
        (WordSemStateFiniteExact.setVars values returned popped) restored lens 0 := by
  obtain ⟨gc, tail, popped, sourceFrame, _, _, _, popShape, popRun, domain,
    valid, continuationRun, continuationIH⟩ :=
    sourceReturningContinuation ac limit values names retCode l1 l2 dest args source sourcePost
      bodyPost result xs args1 prog ss envs location returned guards ih nonzero execution
      notError bodyRun
  have kBound : 4 < k := by
    have h := callerRelation
    unfold stateRel at h
    aesop (config := { enableSimp := false })
  obtain ⟨positive, canonical, nameBound, physical⟩ :=
    returningCallerLocalObligations k frame values names retCode l1 l2 dest args source
      xs args1 prog ss envs popped.locals guards conventions maximum (by omega) domain
  have callerShape : if frame = 0 then callerSize = 0 else callerSize = frame + 1 := by
    have h := callerRelation
    unfold stateRel at h
    aesop (config := { enableSimp := false })
  have callerSizeEq : callerSize = frame + 1 := by
    rw [if_neg (by omega)] at callerShape
    exact callerShape
  have lengthEq := (not_or.mp valid).2
  have countEq : returned.length - (k - 1) =
      Compiler.Backend.WordToStack.numStackRet k values := by
    unfold Compiler.Backend.WordToStack.numStackRet
    omega
  simp only [compCorrectResult, Option.map_some, compileResult, ne_eq,
    not_true_eq_false, ↓reduceIte] at bodyConclusion
  obtain ⟨bodyRelation, placements⟩ := bodyConclusion
  rw [countEq] at bodyRelation
  subst popped
  obtain ⟨restored, copyRun, restoredRelation⟩ :=
    copyReturnRestoresCallerState ac k frame bodyPost target source.localsSize
      (sptToAList envs.1) gc tail lens values returned (by omega) canonical
      (by omega) (by omega) physical sourceFrame bodyRelation placements
  refine ⟨_, restored, popRun, continuationRun, continuationIH, ?_, ?_⟩
  · rwa [callerSizeEq]
  · rw [callerSizeEq]
    exact restoredRelation

theorem simulateReturningContinuationFromHistory {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (k callerSize frame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (saved target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize frame source saved lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (ih : InductionHypotheses ac limit values names retCode l1 l2 dest args source)
    (safe : CodeSafe limit source.code)
    (supported : noInstallSubprogsHOL (.call (some (values,names,retCode,l1,l2)) dest args none) = true)
    (bounded : ceiling (.call (some (values,names,retCode,l1,l2)) dest args none) ≤ limit)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost target (some (.result location returned)) (some (.result location)) (frame :: lens))
    (initial moved : StackSemStateFiniteExact width C F)
    (bs savedBitmaps finalBitmaps : AppList (BitVec width)) (n savedIndex finalIndex : Nat)
    (destinationCode savedCode returnCode compiled callee : HolProg width)
    (destination : Sum Nat Nat) (bodyExtraClock : Nat)
    (flat : flatExpConventions
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (destinationCompile : callDestNative dest args (k, callerSize, frame) =
      (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, callerSize, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, callerSize, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n) (k, callerSize, frame) =
      (compiled, (finalBitmaps, finalIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ initial.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (initial.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact initial.code loc)
    (preludeRun : StackSemEvaluate.evaluate (.seq destinationCode savedCode, initial) = (none, saved))
    (argumentsRun : StackSemEvaluate.evaluate
      (stackArgsNative destination (args.length + 1) (k, callerSize, frame), saved) = (none, moved))
    (calleeRun : StackSemEvaluate.evaluate
      (callee, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock + bodyExtraClock}) =
      (some (.result location), target)) :
    ∃ (popped : WordSemStateFiniteExact width (Nat × C) F)
      (restored : StackSemStateFiniteExact width C F)
      (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      extraClock ≤ (2 * limit) * (bodyPost.clock - sourcePost.clock) + cost retCode ∧
      WordSemStateFiniteExact.popEnv bodyPost = some popped ∧
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, callerSize, frame) values .skip, target) = (none, restored) ∧
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, callerSize, frame) values returnCode,
          {target with clock := target.clock + extraClock}) = (targetResult, targetPost) ∧
      compCorrectResult ac k callerSize frame source sourcePost targetPost result targetResult lens := by
  obtain ⟨popped, restored, popRun, sourceContinuation, continuationIH, copyRun, restoredRelation⟩ :=
    restoreCallerFromBodyReturn ac limit k callerSize frame calleeSize calleeFrame values names
      retCode l1 l2 dest args source sourcePost bodyPost result location returned saved target
      lens xs args1 prog ss envs guards callerRelation conventions maximum ih nonzero
      execution notError bodyRun bodyConclusion
  obtain ⟨retConventions, retFlat, retMaximum, retLength, retBitmapBound, retBitmapPrefix, retLabels⟩ :=
    continuationCompilationFacts ac k callerSize frame values names retCode l1 l2 dest args
      initial bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode
      returnCode compiled destination conventions flat maximum destinationCompile savedCompile
      returnCompile compilation lengthBound bitmapBound bitmapPrefix labels
  obtain ⟨bitmapGrowth, codeGrowth⟩ := returningHistoryGrowth initial saved moved target restored
    (.seq destinationCode savedCode)
    (stackArgsNative destination (args.length + 1) (k, callerSize, frame)) callee
    k callerSize frame l1 l2 bodyExtraClock values (some (.result location))
    preludeRun argumentsRun calleeRun copyRun
  have restoredLabels : ∀ loc, StackSem.getLabelsExact returnCode loc →
      StackSem.locCheckExact restored.code loc := by
    intro loc member
    exact LocationLabels.locCheckSubset initial.code restored.code codeGrowth loc (retLabels loc member)
  have calleeSafe := codeSafe_findCode safe guards.2.2.1
  have safeBody : CodeSafe limit bodyPost.code := codeSafe_evaluate
    (by simpa only [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
      WordSemStateFiniteExact.decClock] using safe) calleeSafe.1 bodyRun
  have safePopped : CodeSafe limit (WordSemStateFiniteExact.setVars values returned popped).code := by
    change CodeSafe limit popped.code
    rw [popEnvCode bodyPost popped popRun]
    exact safeBody
  have retSafe := callReturnSafe limit values names retCode l1 l2 dest args none supported bounded
  obtain ⟨extraClock, targetPost, targetResult, budget, targetContinuation, conclusion⟩ :=
    executeReturningContinuation ac limit k callerSize frame values retCode
      (WordSemStateFiniteExact.setVars values returned popped) sourcePost target restored result
      savedBitmaps finalBitmaps savedIndex finalIndex returnCode lens continuationIH safePopped retSafe.1 retSafe.2
      sourceContinuation notError restoredRelation retConventions retFlat returnCompile retLength
      (retBitmapBound.trans bitmapGrowth.length_le)
      (retBitmapPrefix.trans (bitmapGrowth.drop _)) restoredLabels retMaximum copyRun
  obtain ⟨gc, tail, sourceFrame, _, _, sourceHandler, _, _⟩ :=
    returnedCallerFrame prog source bodyPost envs args1 ss location returned bodyRun
  have poppedHandler : popped.handler = bodyPost.handler := by
    have pop := popRun
    rw [WordSemStateFiniteExact.popEnv, sourceFrame] at pop
    have shape := Option.some.inj pop
    rw [← shape]
  have handler : (WordSemStateFiniteExact.setVars values returned popped).handler = source.handler :=
    poppedHandler.trans sourceHandler
  rw [returningResultInitialHandler ac k callerSize frame source
    (WordSemStateFiniteExact.setVars values returned popped) sourcePost targetPost
    result targetResult lens handler] at conclusion
  have popClock := WordSemStateFiniteExact.popEnv_clock bodyPost popped popRun
  exact ⟨popped, restored, extraClock, targetPost, targetResult,
    by simpa only [WordSemStateFiniteExact.setVars, popClock] using budget, popRun, copyRun,
    targetContinuation, conclusion⟩

theorem simulatePreparedCalleeBody {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps : AppList (BitVec width)) (n savedIndex : Nat)
    (destinationCode savedCode : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) = (savedCode, (savedBitmaps, savedIndex)))
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend savedBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
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
    (space : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤ target.stackSpace) :
    ∃ (destinationTarget saved moved : StackSemStateFiniteExact width C F)
      (location calleeSize calleeFrame : Nat) (body : HolProg width)
      (calleeBs calleeBsPost : AppList (BitVec width)) (calleeIndex calleeIndexPost : Nat),
      StackSemEvaluate.evaluate (destinationCode, target) = (none, destinationTarget) ∧
      StackSemEvaluate.evaluate (savedCode, destinationTarget) = (none, saved) ∧
      StackSemEvaluate.evaluate (stackArgsNative destination (args.length + 1) (k, f, frame), saved) =
        (none, moved) ∧
      stateRel ac k f frame source saved lens 0 ∧
      stateRel ac k 0 0
        {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
        saved (frame :: lens) 0 ∧
      sptLookup location source.code = some (args1.length, prog) ∧
      sptLookup location saved.code = some
        (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) ∧
      compNative ac false prog (calleeBs, calleeIndex) (k, calleeSize, calleeFrame) =
        (body, (calleeBsPost, calleeIndexPost)) ∧
      postAllocConventionsHOL k prog = true ∧ flatExpConventions prog = true ∧
      (appListAppend calleeBs).length ≤ calleeIndex ∧
      calleeIndex - (appListAppend calleeBs).length ≤ target.bitmaps.length ∧
      (appListAppend calleeBsPost).IsPrefix
        (target.bitmaps.drop (calleeIndex - (appListAppend calleeBs).length)) ∧
      ss.getD calleeSize = calleeSize ∧
      (if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1) ∧
      args1.length - k ≤ calleeFrame ∧ maxVarHOL prog < 2 * calleeFrame + 2 * k ∧
      calleeFrame = max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) ∧
      StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code =
        some (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) ∧
      saved.stackSpace = target.stackSpace ∧
      (calleeSize ≤ target.stackSpace →
        ∃ (entry : StackSemStateFiniteExact width C F) (extraClock : Nat)
          (targetPost : StackSemStateFiniteExact width C F)
          (targetResult : Option (StackSemResult width)),
          extraClock ≤ (2 * limit) * ((source.clock - 1) - bodyPost.clock) + cost prog ∧
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
              (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
            bodyPost targetPost bodyResult targetResult (frame :: lens)) := by
  obtain ⟨destinationTarget, saved, moved, location, calleeSize, calleeFrame, body,
    calleeBs, calleeBsPost, calleeIndex, calleeIndexPost, destinationRun, savedRun, moveRun,
    savedRelation, pushedRelation, sourceCode, savedLookup, bodyCompile, bodyConventions,
    bodyFlat, calleeBitmapLength, calleeBitmapBound, calleeBitmapPrefix, calleeLocalsSize,
    calleeShape, calleeArgumentBound, bodyMaximum, calleeFrameEq, found, savedSpace, movedState⟩ :=
    prepareCalleeDestinationAt ac k f frame values names retCode l1 l2 dest args source target
      lens xs args1 prog ss envs bs savedBitmaps n savedIndex destinationCode savedCode destination
      guards related conventions maximum destinationCompile savedCompile bitmapLength bitmapBound
      bitmapPrefix space
  refine ⟨destinationTarget, saved, moved, location, calleeSize, calleeFrame, body,
    calleeBs, calleeBsPost, calleeIndex, calleeIndexPost, destinationRun, savedRun, moveRun,
    savedRelation, pushedRelation, sourceCode, savedLookup, bodyCompile, bodyConventions,
    bodyFlat, calleeBitmapLength, calleeBitmapBound, calleeBitmapPrefix, calleeLocalsSize,
    calleeShape, calleeArgumentBound, bodyMaximum, calleeFrameEq, found, savedSpace, ?_⟩
  intro calleeSpace
  have destinationGrowth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    destinationCode target destinationTarget none destinationRun).1
  have savedGrowth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    savedCode destinationTarget saved none savedRun).1
  have bitmapGrowth : target.bitmaps.IsPrefix saved.bitmaps :=
    destinationGrowth.trans savedGrowth
  obtain ⟨movedAgain, entry, extraClock, targetPost, targetResult, budget, moveAgain,
    allocationRun, targetRun, calleeRun, conclusion⟩ :=
    simulateCalleeBodyAt ac limit k f frame values names retCode l1 l2 dest args source sourcePost
      bodyPost result bodyResult saved lens xs args1 prog ss envs destinationCode destination
      guards savedRelation pushedRelation conventions maximum destinationCompile ih safe nonzero
      execution notError bodyRun location calleeSize calleeFrame body calleeBs calleeBsPost
      calleeIndex calleeIndexPost savedLookup bodyCompile bodyConventions bodyFlat
      calleeBitmapLength (calleeBitmapBound.trans bitmapGrowth.length_le)
      (calleeBitmapPrefix.trans (bitmapGrowth.drop _)) calleeLocalsSize calleeShape
      calleeArgumentBound bodyMaximum (by rwa [savedSpace])
  have movedEq : movedAgain = moved := congrArg Prod.snd (moveAgain.symm.trans moveRun)
  subst movedAgain
  exact ⟨entry, extraClock, targetPost, targetResult, budget, allocationRun, targetRun, calleeRun,
    conclusion⟩

end InitECandidate.Solver.WordToStackBound.CallReturning
#print axioms InitECandidate.Solver.WordToStackBound.CallReturning.sourceReturningContinuation
#print axioms InitECandidate.Solver.WordToStackBound.CallReturning.restoreCallerFromBodyReturn
#print axioms InitECandidate.Solver.WordToStackBound.CallReturning.simulateReturningContinuationFromHistory
#print axioms InitECandidate.Solver.WordToStackBound.CallReturning.simulatePreparedCalleeBody
