import InitECandidate.Solver.StackRemoveDirect.Safety
import InitECandidate.Solver.StackRemoveBound.Atoms
import InitECandidate.Solver.StackRemoveBound.Control
import InitECandidate.Solver.StackRemoveBound.Instructions
import InitECandidate.Solver.StackRemoveBound.Locations
import InitECandidate.Solver.StackRemoveBound.Space
import InitECandidate.Solver.StackRemoveBound.Seq
import InitECandidate.Solver.StackRemoveBound.If
import InitECandidate.Solver.StackRemoveBound.Loop
import InitECandidate.Solver.StackRemoveBound.HeapOperation
import InitECandidate.Solver.StackRemoveBound.StackMemory
import InitECandidate.Solver.StackRemoveBound.StackMemoryAny
import InitECandidate.Solver.StackRemoveBound.StackSize
import InitECandidate.Solver.StackRemoveBound.StoreTransfers
import InitECandidate.Solver.StackRemoveBound.FFI
import InitECandidate.Solver.StackRemoveBound.Bitmap
import InitECandidate.Solver.StackRemoveBound.CodeBufferWrite
import InitECandidate.Solver.StackRemoveBound.DataBufferWrite
import InitECandidate.Solver.StackRemoveBound.ShMemOp
import InitECandidate.Solver.StackRemoveBound.Call
import InitECandidate.Solver.StackRemoveBound.RawCall
import InitECandidate.Solver.StackRemoveBound.JumpLower

/-! Quantitative Stack removal, under explicit absence of Install/StoreConsts
in reachable bodies, allowing unrestricted code at unreachable label 6. All
calls are direct and avoid 6. The full
original state relation, execution and register bounds remain premises. -/
namespace InitECandidate.Solver.StackRemoveDirect
open InitECandidate.Solver.StackRemoveBound
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps StackSemControl StackSemMeasure
local macro "normalize_result" r:ident "using" proof:term : tactic =>
  `(tactic| (
    rcases ($proof:term) with ⟨clock, post, small, run, relation⟩
    refine ⟨clock, post, small, run, ?_⟩
    cases $r:ident with
    | none => exact relation
    | some returned => cases returned <;> exact relation))

/-- Flapjack-only induction infrastructure on the exact evaluator's original
clock-first lexicographic measure. Every recursive premise is discharged at
its actual source call site, using its source guard and clock law. -/
private theorem correctnessMeasure {width : Nat} [NeZero width] {C F : Type} :
    ∀ (measure : Nat × Nat) (program : HolProg width) (source : StackSemStateFiniteExact width C F),
      stackSemMeasure program source = measure →
      supported program = true → StateSafe source →
      ∀ (result : Option (StackSemResult width)) (postSource target : StackSemStateFiniteExact width C F)
        (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool),
      ∀ (_hypothesis : evaluate (program, source) = (result, postSource) ∧ result ≠ some .error ∧
        stateRelHOL jump bounds pointer source target ∧ StackProps.regBound program pointer),
      ∃ clock postTarget, clock ≤ resultBudget result ∧
        evaluate (comp jump bounds pointer program, {target with clock := clock + target.clock}) =
          (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  intro measure
  induction measure using Compiler.Backend.StackProps.EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
  intro program source hm programSafe stateSafe result postSource target pointer bounds jump hypothesis
  subst hm
  cases program
  case install => simp only [supported, Bool.false_eq_true] at programSafe
  case storeConsts => simp only [supported, Bool.false_eq_true] at programSafe
  all_goals first
    | solve | refine (by normalize_result result using (compCorrectFFI _ _ _ _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectGet _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectSet _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectBitmapLoad _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectDataBufferWrite _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectSkip _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectHalt _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectAlloc _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectStackLoadAny _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectStackStoreAny _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectLocValue _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectTick _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectReturn _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectRaise _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectBreak _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectContinue _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectShMemOp _ _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectStackFree _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectStackAlloc _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectOpCurrHeap _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectStackLoad _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectStackStore _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectInst _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectCodeBufferWrite _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectStackGetSize _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectStackSetSize _ _ _ _ _ _ _ _ hypothesis))
    | skip
  case seq first second =>
    refine (by normalize_result result using (compCorrectSeq first second source result postSource target pointer bounds jump ?_ ?_ hypothesis))
    · intro r post t k off j h
      normalize_result r using (ih _ (seq_first_measure_lt first second source) first source rfl (Bool.and_eq_true_iff.mp programSafe).1 stateSafe r post t k off j h)
    · intro middle firstRun
      have smaller := seq_second_measure_lt first second source ((none : Option (StackSemResult width)), middle)
      have unclamped := StackSemEvaluateClock.fixClockEvaluate first source
      rw [firstRun] at unclamped
      rw [unclamped] at smaller
      intro r post t k off j h
      normalize_result r using (ih _ smaller second middle rfl (Bool.and_eq_true_iff.mp programSafe).2
        (stateSafe_evaluate first source middle none stateSafe firstRun) r post t k off j h)
  case ite comparison register operand first second =>
    refine (by normalize_result result using (compCorrectIf comparison register operand first second source result postSource target pointer bounds jump ?_ ?_ hypothesis))
    · intro left right _ _ _ r post t k off j h
      normalize_result r using (ih _ (if_first_measure_lt comparison register operand first second source) first source rfl (Bool.and_eq_true_iff.mp programSafe).1 stateSafe r post t k off j h)
    · intro left right _ _ _ r post t k off j h
      normalize_result r using (ih _ (if_second_measure_lt comparison register operand first second source) second source rfl (Bool.and_eq_true_iff.mp programSafe).2 stateSafe r post t k off j h)
  case loop body =>
    refine (by normalize_result result using (compCorrectLoop body source result postSource target pointer bounds jump ?_ ?_ hypothesis))
    · intro r post t k off j h
      normalize_result r using (ih _ (loop_body_measure_lt body source) body source rfl programSafe stateSafe r post t k off j h)
    · intro bodyResult middle bodyRun _ nonzero
      have unclamped := StackSemEvaluateClock.fixClockEvaluate body source
      rw [bodyRun] at unclamped
      have smaller := loop_reentry_measure_lt body source (bodyResult, middle)
        (by simpa only [unclamped] using nonzero)
      rw [unclamped] at smaller
      intro r post t k off j h
      normalize_result r using (ih _ smaller (.loop body) (decClock middle) rfl programSafe
        (stateSafe_evaluate body source middle bodyResult stateSafe bodyRun) r post t k off j h)
  case jumpLower first second label =>
    refine (by normalize_result result using (compCorrectJumpLower first second label source result postSource target pointer bounds jump ?_ hypothesis))
    · intro left right program _ _ _ lookup nonzero r post t k off j h
      normalize_result r using (ih _ (callee_measure_lt program (.jumpLower first second label) source nonzero) program (decClock source) rfl (stateSafe.1 label program (by simpa [supported] using programSafe) lookup) stateSafe r post t k off j h)
  case rawCall label =>
    refine (by normalize_result result using (compCorrectRawCall label source result postSource target pointer bounds jump ?_ hypothesis))
    · intro frame body lookup nonzero r post t k off j h
      normalize_result r using (ih _ (callee_measure_lt body (.rawCall label) source nonzero) body (decClock source) rfl
        (Bool.and_eq_true_iff.mp (stateSafe.1 label _ (by simpa [supported] using programSafe) lookup)).2 stateSafe r post t k off j h)
  case call ret dest handler =>
    refine (by normalize_result result using (compCorrectCall ret dest handler source result postSource target pointer bounds jump ?_ ?_ ?_ hypothesis))
    · cases ret with
      | none =>
        intro program lookup _ nonzero r post t k off j h
        normalize_result r using (ih _ (callee_measure_lt program (.call none dest handler) source nonzero) program (decClock source) rfl
          (supported_findCode dest source.regs source.code program stateSafe.1 (supported_dest _ _ _ programSafe) lookup) stateSafe r post t k off j h)
      | some entry =>
        rcases entry with ⟨body, link, l1, l2⟩
        intro program lookup nonzero
        have smaller := callee_measure_lt program (.call (some (body, link, l1, l2)) dest handler)
          (setVar link (.loc l1 l2) source) nonzero
        intro r post t k off j h
        normalize_result r using (ih _ smaller program (decClock (setVar link (.loc l1 l2) source)) rfl
          (supported_findCode dest (source.regs.eraseEq link) source.code program stateSafe.1 (supported_dest _ _ _ programSafe) lookup) stateSafe r post t k off j h)
    · cases ret with
      | none => trivial
      | some entry =>
        rcases entry with ⟨body, link, l1, l2⟩
        intro program middle _ nonzero calleeRun
        have unclamped := StackSemEvaluateClock.fixClockEvaluate program (decClock (setVar link (.loc l1 l2) source))
        rw [calleeRun] at unclamped
        have smaller := call_continuation_measure_lt body (.call (some (body, link, l1, l2)) dest handler)
          source link l1 l2 ((some (.result (.loc l1 l2)) : Option (StackSemResult width)), middle) nonzero
        rw [unclamped] at smaller
        intro r post t k off j h
        normalize_result r using (ih _ smaller body middle rfl
          (supported_return body link l1 l2 dest handler programSafe)
          (stateSafe_evaluate program (decClock (setVar link (.loc l1 l2) source)) middle _ stateSafe calleeRun) r post t k off j h)
    · cases ret with
      | none => trivial
      | some entry =>
        rcases entry with ⟨body, link, l1, l2⟩
        cases handler with
        | none => trivial
        | some handlerEntry =>
          rcases handlerEntry with ⟨handlerBody, hl1, hl2⟩
          intro program middle _ nonzero calleeRun
          have unclamped := StackSemEvaluateClock.fixClockEvaluate program (decClock (setVar link (.loc l1 l2) source))
          rw [calleeRun] at unclamped
          have smaller := call_continuation_measure_lt handlerBody
            (.call (some (body, link, l1, l2)) dest (some (handlerBody, hl1, hl2)))
            source link l1 l2 ((some (.exception (.loc hl1 hl2)) : Option (StackSemResult width)), middle) nonzero
          rw [unclamped] at smaller
          intro r post t k off j h
          normalize_result r using (ih _ smaller handlerBody middle rfl
            (supported_handler (some (body, link, l1, l2)) dest handlerBody hl1 hl2 programSafe)
            (stateSafe_evaluate program (decClock (setVar link (.loc l1 l2) source)) middle _ stateSafe calleeRun) r post t k off j h)

theorem compCorrect {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (programSafe : supported program = true) (stateSafe : StateSafe source)
    (hypothesis : evaluate (program, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound program pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      evaluate (comp jump bounds pointer program,
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  normalize_result result using (correctnessMeasure (stackSemMeasure program source)
    program source rfl programSafe stateSafe result postSource target pointer bounds jump hypothesis)

end InitECandidate.Solver.StackRemoveDirect
#print axioms InitECandidate.Solver.StackRemoveDirect.compCorrect
