import InitECandidate.Solver.StackRemoveBound.Assembly
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitClock

/-! Whole-entry Stack removal and its clock-neutral initialization prefix.
The actual initializer execution and full state relation remain premises. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open StackLang StackSemEvaluate

theorem entrySimulation {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start clock : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (safe : StateSafe source)
    (relation : stateRelHOL jump bounds pointer source target)
    (run : evaluate (.call none (.inl start) none, {source with clock := clock}) =
      (result, postSource)) (nonError : result ≠ some .error) :
    ∃ extra postTarget, extra ≤ resultBudget result ∧
      evaluate (.call none (.inl start) none, {target with clock := extra + clock}) =
        (result, postTarget) ∧ postTarget.ffi = postSource.ffi := by
  obtain ⟨extra, postTarget, small, targetRun, postRelation⟩ :=
    compCorrect (.call none (.inl start) none)
      {source with clock := clock} result postSource {target with clock := clock}
      pointer bounds jump rfl safe ⟨run, nonError,
        RelationLaws.stateRelWithClock jump bounds pointer clock source target relation,
        by simp [StackProps.regBound]⟩
  refine ⟨extra, postTarget, small, ?_, ?_⟩
  · simpa only [comp] using targetRun
  · cases result with
    | none => exact (RelationLaws.stateRelConst jump bounds pointer postSource postTarget postRelation).2.2.2.2.1
    | some value =>
      cases value
      all_goals first
        | exact postRelation
        | exact (RelationLaws.stateRelConst jump bounds pointer postSource postTarget postRelation).2.2.2.2.1

theorem initializedEntry {width : Nat} [NeZero width] {C F : Type}
    (generateGc jump : Bool) (maximumHeap pointer start clock : Nat)
    (bounds : BitVec width × BitVec width)
    (source boot target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (safe : StateSafe source)
    (initialized : evaluate (initCode generateGc maximumHeap pointer, boot) = (none, target))
    (relation : stateRelHOL jump bounds pointer source target)
    (run : evaluate (.call none (.inl start) none, {source with clock := clock}) =
      (result, postSource)) (nonError : result ≠ some .error) :
    ∃ extra postTarget, extra ≤ 1 ∧
      evaluate (.seq (initCode generateGc maximumHeap pointer) (.call none (.inl start) none),
        {boot with clock := extra + clock}) = (result, postTarget) ∧
      postTarget.ffi = postSource.ffi := by
  obtain ⟨extra, postTarget, small, targetRun, ffi⟩ :=
    entrySimulation jump bounds pointer start clock source target postSource result safe relation run nonError
  have ceiling : resultBudget result ≤ 1 := by
    cases result with
    | none => simp [resultBudget]
    | some value => cases value <;> simp [resultBudget]
  refine ⟨extra, postTarget, small.trans ceiling, ?_, ffi⟩
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
    StackRemove.Proofs.InitClock.evaluateInitCodeClock generateGc maximumHeap pointer
      boot target none (extra + clock) initialized]
  exact targetRun

end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.entrySimulation
#print axioms InitECandidate.Solver.StackRemoveBound.initializedEntry
