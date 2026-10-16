import InitECandidate.Solver.WordToStackBound.Handler
import InitECandidate.Solver.WordToStackBound.CallReturningNone
import InitECandidate.Solver.WordToStackBound.CallTail

namespace InitECandidate.Solver.WordToStackBound.Call
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

def OriginalInductionHypotheses {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat)
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F) : Prop :=
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs v5 s2 v8 x ys s1,
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 ∧
        WordSemStateFiniteExact.evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock source))) = (v5, s2) ∧
        v5 = some v8 ∧ v8 = .result x ys ∧ ¬ (x ≠ .loc originalL1 originalL2 ∨ ys.length ≠ n.length) ∧
        WordSemStateFiniteExact.popEnv s2 = some s1 ∧ sptDomainEqUnion s1.locals envs.1 envs.2 →
      Simulation ac limit retHandler (WordSemStateFiniteExact.setVars n ys s1)) ∧
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs v5 s2 v8 x' y v n' v2 h
        v4 originalL1' originalL2',
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 ∧
        WordSemStateFiniteExact.evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock source))) = (v5, s2) ∧
        v5 = some v8 ∧ v8 = .exception x' y ∧ handler = some v ∧ v = (n', v2) ∧ v2 = (h, v4) ∧
        v4 = (originalL1', originalL2') ∧ x' = .loc originalL1' originalL2' ∧ sptDomainEqUnion s2.locals envs.1 envs.2 →
      Simulation ac limit h (WordSemStateFiniteExact.setVar n' y s2)) ∧
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs,
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 →
      Simulation ac limit prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock source)))) ∧
    (∀ xs v3 args1 v10 prog ss,
      WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
      wordSemFindCode dest (wordSemAddRetLoc ret xs) source.code source.stackSize = some v3 ∧
      v3 = (args1,v10) ∧ v10 = (prog,ss) ∧ ret = none ∧ handler = none ∧ source.clock ≠ 0 →
      Simulation ac limit prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock source)))

theorem returningCallCase {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : OriginalInductionHypotheses ac limit (some (values,names,retCode,l1,l2)) dest args handler source) :
    Simulation ac limit (.call (some (values,names,retCode,l1,l2)) dest args handler) source := by
  cases handler with
  | none =>
    apply CallReturning.compCorrectCallReturningNone ac limit values names retCode l1 l2 dest args source
    refine ⟨?_,?_⟩
    · intro xs args1 prog ss envs location ys calleePost popped facts
      rcases facts with ⟨⟨get,bad,find,valid,cut⟩,clock,run,checked,pop,domain⟩
      exact ih.1 xs (args1,prog,ss) args1 (prog,ss) prog ss
        (values,names,retCode,l1,l2) values (names,retCode,l1,l2) names (retCode,l1,l2)
        retCode (l1,l2) l1 l2 envs (some (.result location ys)) calleePost
        (.result location ys) location ys popped
        ⟨get,bad,find,rfl,rfl,rfl,rfl,rfl,rfl,rfl,valid,cut,clock,run,rfl,rfl,checked,pop,domain⟩
    · intro xs args1 prog ss envs facts
      rcases facts with ⟨⟨get,bad,find,valid,cut⟩,clock⟩
      exact ih.2.2.1 xs (args1,prog,ss) args1 (prog,ss) prog ss
        (values,names,retCode,l1,l2) values (names,retCode,l1,l2) names (retCode,l1,l2)
        retCode (l1,l2) l1 l2 envs
        ⟨get,bad,find,rfl,rfl,rfl,rfl,rfl,rfl,rfl,valid,cut,clock⟩
  | some descriptor =>
    rcases descriptor with ⟨handlerVar,handlerCode,h1,h2⟩
    exact CallReturningHandler.compCorrectCallReturningHandler ac limit values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source ⟨ih.1,ih.2.1,ih.2.2.1⟩

theorem compCorrectCall {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat)
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : OriginalInductionHypotheses ac limit ret dest args handler source) :
    Simulation ac limit (.call ret dest args handler) source := by
  cases ret with
  | none =>
    intro safe _supported _bounded k f frame sourcePost target result bs bsPost n nPost compiled lens facts
    apply CallTail.compCorrectCallTail ac limit dest args handler source safe ?_ k f frame sourcePost target
      result bs bsPost n nPost compiled lens facts
    intro xs args1 prog ss guards
    obtain ⟨get,bad,find,noHandler,clock⟩ := guards
    exact ih.2.2.2 xs (args1,prog,ss) args1 (prog,ss) prog ss
      ⟨get,bad,find,rfl,rfl,rfl,noHandler,clock⟩
  | some descriptor =>
    rcases descriptor with ⟨values,names,retCode,l1,l2⟩
    exact returningCallCase ac limit values names retCode l1 l2 dest args handler source ih

#print axioms InitECandidate.Solver.WordToStackBound.Call.returningCallCase
#print axioms InitECandidate.Solver.WordToStackBound.Call.compCorrectCall

end InitECandidate.Solver.WordToStackBound.Call
