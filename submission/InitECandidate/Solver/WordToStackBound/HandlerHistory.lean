import InitECandidate.Solver.WordToStackBound.HandlerBranches
import InitECandidate.Solver.WordToStackBound.HandlerClock
import InitECandidate.Solver.WordToStackBound.CallBudget

namespace InitECandidate.Solver.WordToStackBound.CallReturningHandler
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
open Flapjack.WordToStackProofs.CallReturnHandler

theorem normalCompiledHandlerCallFromHistory {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (k frame payload : Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (originalTarget target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (prior : stateRel ac k frame payload source originalTarget lens 0)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : Flapjack.WordToStackProofs.CompCorrect.CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (ih : InductionHypotheses ac limit values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source)
    (safe : CodeSafe limit source.code)
    (supported : noInstallSubprogsHOL (.call (some (values,names,retCode,l1,l2)) dest args
      (some (handlerVar,handlerCode,h1,h2))) = true)
    (bounded : ceiling (.call (some (values,names,retCode,l1,l2)) dest args
      (some (handlerVar,handlerCode,h1,h2))) ≤ limit)
    (conventions : postAllocConventionsHOL k
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (flat : flatExpConventions
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) < 2*payload+2*k)
    (nonzero : source.clock ≠ 0) (result : Option (WordSemResult width))
    (wholeRun : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (location : WordLocW width) (returnedValues : List (WordLocW width))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returnedValues),bodyPost))
    (calleeSize calleeFrame : Nat)
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) bodyPost target
      (some (.result location returnedValues)) (some (.result location)) (payload::lens))
    (moved : StackSemStateFiniteExact width C F) (destination : Sum Nat Nat)
    (calleeCode : HolProg width) (bodyExtra : Nat)
    (bodyBudget : bodyExtra ≤ (2 * limit) * ((source.clock - 1) - bodyPost.clock) + cost prog)
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some calleeCode)
    (calleeRun : StackSemEvaluate.evaluate
      (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock+bodyExtra}) =
      (some (.result location),target))
    (bs savedBs retBs handlerBs : AppList (BitVec width))
    (n savedIndex retIndex handlerIndex : Nat)
    (destinationCode savedCode returnCode handlerTarget compiled : HolProg width)
    (destinationCompile : callDestNative dest args (k,frame,payload) = (destinationCode,destination))
    (savedCompile : wLiveNative names (bs,n) (k,frame,payload) = (savedCode,(savedBs,savedIndex)))
    (returnCompile : compNative ac false retCode (savedBs,savedIndex) (k,frame,payload) =
      (returnCode,(retBs,retIndex)))
    (handlerCompile : compNative ac false handlerCode (retBs,retIndex) (k,frame,payload) =
      (handlerTarget,(handlerBs,handlerIndex)))
    (compilation : compNative ac false
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) (bs,n) (k,frame,payload) =
      (compiled,(handlerBs,handlerIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ originalTarget.bitmaps.length)
    (bitmapPrefix : (appListAppend handlerBs).IsPrefix
      (originalTarget.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact originalTarget.code loc)
    (preludeRun : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
        (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),originalTarget) =
      (none,moved)) :
    ∃ extra targetPost targetResult,
      extra ≤ (2 * limit) * (source.clock - sourcePost.clock) ∧
      StackSemEvaluate.evaluate (compiled,{originalTarget with clock := originalTarget.clock+extra}) =
        (targetResult,targetPost) ∧
      compCorrectResult ac k frame payload source sourcePost targetPost result targetResult lens := by
  have free := completeHandlerPreludeClockFree (C := C) (F := F) k frame payload h1 h2 dest args names
    (bs,n) (savedBs,savedIndex) destinationCode savedCode destination destinationCompile savedCompile
  have fixed := free originalTarget originalTarget.clock
  change StackSemEvaluate.evaluate
    (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
      (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),originalTarget) =
    (Prod.map id (fun state => {state with clock := originalTarget.clock}))
      (StackSemEvaluate.evaluate
        (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
          (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),originalTarget)) at fixed
  rw [preludeRun] at fixed
  have clockEq : moved.clock = originalTarget.clock :=
    congrArg (fun state => state.clock) (Prod.mk.inj fixed).2
  have movedNonzero : moved.clock ≠ 0 := by
    rw [clockEq,← prior.1]
    exact nonzero
  have growth := handlerCalleeHistoryGrowth originalTarget moved target
    (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
      (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))))
    calleeCode l1 l2 bodyExtra (some (.result location)) preludeRun calleeRun
  obtain ⟨continuationLength,continuationBound,continuationPrefix,continuationLabels⟩ :=
    handlerReturningCompilationContext ac k frame payload values names retCode handlerCode l1 l2 h1 h2 handlerVar
      dest args bs savedBs retBs handlerBs n savedIndex retIndex handlerIndex destinationCode savedCode
      returnCode handlerTarget compiled destination originalTarget destinationCompile savedCompile
      returnCompile handlerCompile compilation lengthBound bitmapBound bitmapPrefix labels
  have bodyLabels : ∀ loc, StackSem.getLabelsExact returnCode loc →
      StackSem.locCheckExact target.code loc := by
    intro loc member
    exact LocationLabels.locCheckSubset originalTarget.code target.code growth.2 loc
      (continuationLabels loc member)
  obtain ⟨continuationExtra,targetPost,targetResult,continuationBudget,callRun,conclusion⟩ :=
    normalHandlerCallFromCallee ac limit k frame payload source sourcePost bodyPost originalTarget target
      lens prior values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1 prog ss envs
      guards ih safe supported bounded conventions flat maximum nonzero result wholeRun notError location returnedValues
      bodyRun calleeSize calleeFrame bodyConclusion moved destination calleeCode handlerTarget bodyExtra found movedNonzero calleeRun
      savedBs retBs savedIndex retIndex returnCode returnCompile
      continuationLength (continuationBound.trans growth.1.length_le)
      (continuationPrefix.trans (growth.1.drop _)) bodyLabels
  have bodyDecrease : bodyPost.clock ≤ source.clock - 1 :=
    (WordSemStateFiniteExact.evaluate_clock prog _ _ _ bodyRun).1
  have tailDecrease := handlerSourceCallTailClock values names retCode handlerCode l1 l2 handlerVar h1 h2
    dest args source sourcePost bodyPost result (some (.result location returnedValues)) xs args1 prog ss envs guards nonzero wholeRun bodyRun
  have calleeSafe := codeSafe_findCode safe guards.2.2.1
  have selectedSafe := callReturnSafe limit values names retCode l1 l2 dest args
    (some (handlerVar,handlerCode,h1,h2)) supported bounded
  have budget := callBudget limit source.clock bodyPost.clock sourcePost.clock bodyExtra
    continuationExtra (cost prog) (cost retCode) nonzero bodyDecrease tailDecrease
    ((cost_le_ceiling prog).trans calleeSafe.2) ((cost_le_ceiling retCode).trans selectedSafe.2)
    bodyBudget continuationBudget
  exact ⟨bodyExtra+continuationExtra,targetPost,targetResult,budget,
    completeHandlerCallFromPrelude ac k frame payload values names retCode handlerCode l1 l2 handlerVar
      h1 h2 dest args bs savedBs retBs handlerBs n savedIndex retIndex handlerIndex destinationCode savedCode
      returnCode handlerTarget compiled destination originalTarget moved targetPost
      (bodyExtra+continuationExtra) targetResult destinationCompile savedCompile returnCompile handlerCompile
      compilation preludeRun callRun,conclusion⟩

theorem exceptionCompiledHandlerCallFromHistory {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (k frame payload : Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (originalTarget target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (prior : stateRel ac k frame payload source originalTarget lens 0)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : Flapjack.WordToStackProofs.CompCorrect.CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (ih : InductionHypotheses ac limit values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source)
    (safe : CodeSafe limit source.code)
    (supported : noInstallSubprogsHOL (.call (some (values,names,retCode,l1,l2)) dest args
      (some (handlerVar,handlerCode,h1,h2))) = true)
    (bounded : ceiling (.call (some (values,names,retCode,l1,l2)) dest args
      (some (handlerVar,handlerCode,h1,h2))) ≤ limit)
    (conventions : postAllocConventionsHOL k
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (flat : flatExpConventions
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) < 2*payload+2*k)
    (nonzero : source.clock ≠ 0) (result : Option (WordSemResult width))
    (wholeRun : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (location value : WordLocW width)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.exception location value),bodyPost))
    (calleeSize calleeFrame : Nat)
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) bodyPost target
      (some (.exception location value)) (some (.exception location)) (payload::lens))
    (moved : StackSemStateFiniteExact width C F) (destination : Sum Nat Nat)
    (calleeCode : HolProg width) (bodyExtra : Nat)
    (bodyBudget : bodyExtra ≤ (2 * limit) * ((source.clock - 1) - bodyPost.clock) + cost prog)
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some calleeCode)
    (calleeRun : StackSemEvaluate.evaluate
      (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock+bodyExtra}) =
      (some (.exception location),target))
    (bs savedBs retBs handlerBs : AppList (BitVec width))
    (n savedIndex retIndex handlerIndex : Nat)
    (destinationCode savedCode returnCode handlerTarget compiled : HolProg width)
    (destinationCompile : callDestNative dest args (k,frame,payload) = (destinationCode,destination))
    (savedCompile : wLiveNative names (bs,n) (k,frame,payload) = (savedCode,(savedBs,savedIndex)))
    (returnCompile : compNative ac false retCode (savedBs,savedIndex) (k,frame,payload) =
      (returnCode,(retBs,retIndex)))
    (handlerCompile : compNative ac false handlerCode (retBs,retIndex) (k,frame,payload) =
      (handlerTarget,(handlerBs,handlerIndex)))
    (compilation : compNative ac false
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) (bs,n) (k,frame,payload) =
      (compiled,(handlerBs,handlerIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ originalTarget.bitmaps.length)
    (bitmapPrefix : (appListAppend handlerBs).IsPrefix
      (originalTarget.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact originalTarget.code loc)
    (preludeRun : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
        (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),originalTarget) =
      (none,moved)) :
    ∃ extra targetPost targetResult,
      extra ≤ (2 * limit) * (source.clock - sourcePost.clock) ∧
      StackSemEvaluate.evaluate (compiled,{originalTarget with clock := originalTarget.clock+extra}) =
        (targetResult,targetPost) ∧
      compCorrectResult ac k frame payload source sourcePost targetPost result targetResult lens := by
  have free := completeHandlerPreludeClockFree (C := C) (F := F) k frame payload h1 h2 dest args names
    (bs,n) (savedBs,savedIndex) destinationCode savedCode destination destinationCompile savedCompile
  have fixed := free originalTarget originalTarget.clock
  change StackSemEvaluate.evaluate
    (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
      (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),originalTarget) =
    (Prod.map id (fun state => {state with clock := originalTarget.clock}))
      (StackSemEvaluate.evaluate
        (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
          (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),originalTarget)) at fixed
  rw [preludeRun] at fixed
  have clockEq : moved.clock = originalTarget.clock :=
    congrArg (fun state => state.clock) (Prod.mk.inj fixed).2
  have movedNonzero : moved.clock ≠ 0 := by
    rw [clockEq,← prior.1]
    exact nonzero
  have growth := handlerCalleeHistoryGrowth originalTarget moved target
    (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
      (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))))
    calleeCode l1 l2 bodyExtra (some (.exception location)) preludeRun calleeRun
  obtain ⟨continuationLength,continuationBound,continuationPrefix,continuationLabels⟩ :=
    handlerExceptionCompilationContext ac k frame payload values names retCode handlerCode l1 l2 h1 h2 handlerVar
      dest args bs savedBs retBs handlerBs n savedIndex retIndex handlerIndex destinationCode savedCode
      returnCode handlerTarget compiled destination originalTarget destinationCompile savedCompile
      returnCompile handlerCompile compilation lengthBound bitmapBound bitmapPrefix labels
  have bodyLabels : ∀ loc, StackSem.getLabelsExact handlerTarget loc →
      StackSem.locCheckExact target.code loc := by
    intro loc member
    exact LocationLabels.locCheckSubset originalTarget.code target.code growth.2 loc
      (continuationLabels loc member)
  obtain ⟨continuationExtra,targetPost,targetResult,continuationBudget,callRun,conclusion⟩ :=
    exceptionHandlerCallFromCallee ac limit k frame payload source sourcePost bodyPost originalTarget target
      lens prior values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1 prog ss envs
      guards ih safe supported bounded conventions flat maximum nonzero result wholeRun notError location value
      bodyRun calleeSize calleeFrame bodyConclusion moved destination calleeCode (.seq .skip (copyRetNative false true (k,frame,payload) values
        (popHandlerNative false (k,frame,payload) returnCode))) bodyExtra found movedNonzero calleeRun
      retBs handlerBs retIndex handlerIndex handlerTarget handlerCompile
      continuationLength (continuationBound.trans growth.1.length_le)
      (continuationPrefix.trans (growth.1.drop _)) bodyLabels
  have bodyDecrease : bodyPost.clock ≤ source.clock - 1 :=
    (WordSemStateFiniteExact.evaluate_clock prog _ _ _ bodyRun).1
  have tailDecrease := handlerSourceCallTailClock values names retCode handlerCode l1 l2 handlerVar h1 h2
    dest args source sourcePost bodyPost result (some (.exception location value)) xs args1 prog ss envs guards nonzero wholeRun bodyRun
  have calleeSafe := codeSafe_findCode safe guards.2.2.1
  have selectedSafe := callHandlerSafe limit (some (values,names,retCode,l1,l2))
    handlerVar handlerCode h1 h2 dest args supported bounded
  have budget := callBudget limit source.clock bodyPost.clock sourcePost.clock bodyExtra
    continuationExtra (cost prog) (cost handlerCode) nonzero bodyDecrease tailDecrease
    ((cost_le_ceiling prog).trans calleeSafe.2) ((cost_le_ceiling handlerCode).trans selectedSafe.2)
    bodyBudget continuationBudget
  exact ⟨bodyExtra+continuationExtra,targetPost,targetResult,budget,
    completeHandlerCallFromPrelude ac k frame payload values names retCode handlerCode l1 l2 handlerVar
      h1 h2 dest args bs savedBs retBs handlerBs n savedIndex retIndex handlerIndex destinationCode savedCode
      returnCode handlerTarget compiled destination originalTarget moved targetPost
      (bodyExtra+continuationExtra) targetResult destinationCompile savedCompile returnCompile handlerCompile
      compilation preludeRun callRun,conclusion⟩

end InitECandidate.Solver.WordToStackBound.CallReturningHandler
#print axioms InitECandidate.Solver.WordToStackBound.CallReturningHandler.normalCompiledHandlerCallFromHistory
#print axioms InitECandidate.Solver.WordToStackBound.CallReturningHandler.exceptionCompiledHandlerCallFromHistory
