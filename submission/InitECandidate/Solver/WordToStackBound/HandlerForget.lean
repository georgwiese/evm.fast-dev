import InitECandidate.Solver.WordToStackBound.HandlerHypotheses

namespace InitECandidate.Solver.WordToStackBound.CallReturningHandler
open Flapjack Flapjack.Compiler.Encoders.Asm

theorem forgetHypotheses {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : InductionHypotheses ac limit values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source)
    (safe : CodeSafe limit source.code)
    (supported : noInstallSubprogsHOL (.call (some (values,names,retCode,l1,l2)) dest args
      (some (handlerVar,handlerCode,h1,h2))) = true)
    (bounded : ceiling (.call (some (values,names,retCode,l1,l2)) dest args
      (some (handlerVar,handlerCode,h1,h2))) ≤ limit) :
    Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler.InductionHypotheses ac
      values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source := by
  have retSafe := callReturnSafe limit values names retCode l1 l2 dest args
    (some (handlerVar,handlerCode,h1,h2)) supported bounded
  have handlerSafe := callHandlerSafe limit (some (values,names,retCode,l1,l2))
    handlerVar handlerCode h1 h2 dest args supported bounded
  refine ⟨?_,?_,?_⟩
  · intro xs args1 prog ss envs location ys calleePost popped facts
    obtain ⟨guards,nonzero,run,checked,pop,domain⟩ := facts
    have bodySafe := codeSafe_findCode safe guards.2.2.1
    have safePost : CodeSafe limit calleePost.code := codeSafe_evaluate
      (by simpa only [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
        WordSemStateFiniteExact.decClock] using safe) bodySafe.1 run
    have safePopped : CodeSafe limit (WordSemStateFiniteExact.setVars values ys popped).code := by
      change CodeSafe limit popped.code
      rw [popEnvCode calleePost popped pop]
      exact safePost
    exact forgetSimulation ac limit retCode _
      (ih.1 xs args1 prog ss envs location ys calleePost popped ⟨guards,nonzero,run,checked,pop,domain⟩)
      safePopped retSafe.1 retSafe.2
  · intro xs args1 prog ss envs location value calleePost facts
    obtain ⟨guards,nonzero,run,checked,domain⟩ := facts
    have bodySafe := codeSafe_findCode safe guards.2.2.1
    have safePost : CodeSafe limit calleePost.code := codeSafe_evaluate
      (by simpa only [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
        WordSemStateFiniteExact.decClock] using safe) bodySafe.1 run
    exact forgetSimulation ac limit handlerCode _
      (ih.2.1 xs args1 prog ss envs location value calleePost ⟨guards,nonzero,run,checked,domain⟩)
      safePost handlerSafe.1 handlerSafe.2
  · intro xs args1 prog ss envs facts
    obtain ⟨guards,nonzero⟩ := facts
    have bodySafe := codeSafe_findCode safe guards.2.2.1
    exact forgetSimulation ac limit prog _ (ih.2.2 xs args1 prog ss envs ⟨guards,nonzero⟩)
      (by simpa only [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv,
        WordSemStateFiniteExact.decClock] using safe) bodySafe.1 bodySafe.2

end InitECandidate.Solver.WordToStackBound.CallReturningHandler
#print axioms InitECandidate.Solver.WordToStackBound.CallReturningHandler.forgetHypotheses
