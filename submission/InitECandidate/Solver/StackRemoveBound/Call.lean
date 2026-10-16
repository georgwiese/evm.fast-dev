import InitECandidate.Solver.StackRemoveBound.CallTail
import InitECandidate.Solver.StackRemoveBound.CallReturnNone
import InitECandidate.Solver.StackRemoveBound.CallReturnHandler

/-! All call shapes retain the result-dependent clock bound. -/
namespace InitECandidate.Solver.StackRemoveBound
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open StackSemEvaluate StackSemStateOps Compiler.Backend.StackLang

theorem compCorrectCall {width : Nat} [NeZero width] {C F : Type}
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (calleeIH : match ret with
      | none =>
          ∀ (program : HolProg width),
            StackSemControl.findCode dest source.regs source.code = some program →
            handler = none → source.clock ≠ 0 →
            ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
              (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
            evaluate (program, decClock source) = (r, post) ∧ r ≠ some .error ∧
              stateRelHOL j off k (decClock source) t ∧ StackProps.regBound program k →
            ∃ clock postTarget, clock ≤ resultBudget r ∧
              evaluate (comp j off k program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
              (match r with
               | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
               | _ => stateRelHOL j off k post postTarget)
      | some (_body, link, l1, l2) =>
          ∀ (program : HolProg width),
            StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
            source.clock ≠ 0 →
            ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
              (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
            evaluate (program, decClock (setVar link (.loc l1 l2) source)) = (r, post) ∧ r ≠ some .error ∧
              stateRelHOL j off k (decClock (setVar link (.loc l1 l2) source)) t ∧ StackProps.regBound program k →
            ∃ clock postTarget, clock ≤ resultBudget r ∧
              evaluate (comp j off k program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
              (match r with
               | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
               | _ => stateRelHOL j off k post postTarget))
    (returnIH : match ret with
      | none => True
      | some (body, link, l1, l2) =>
          ∀ (program : HolProg width) (middle : StackSemStateFiniteExact width C F),
            StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
            source.clock ≠ 0 →
            evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
              (some (.result (.loc l1 l2)), middle) →
            ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
              (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
            evaluate (body, middle) = (r, post) ∧ r ≠ some .error ∧
              stateRelHOL j off k (middle) t ∧ StackProps.regBound body k →
            ∃ clock postTarget, clock ≤ resultBudget r ∧
              evaluate (comp j off k body, {t with clock := clock + t.clock}) = (r, postTarget) ∧
              (match r with
               | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
               | _ => stateRelHOL j off k post postTarget))
    (handlerIH : match ret, handler with
      | some (_body, link, l1, l2), some (handler, hl1, hl2) =>
          ∀ (program : HolProg width) (middle : StackSemStateFiniteExact width C F),
            StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
            source.clock ≠ 0 →
            evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
              (some (.exception (.loc hl1 hl2)), middle) →
            ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
              (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
            evaluate (handler, middle) = (r, post) ∧ r ≠ some .error ∧
              stateRelHOL j off k (middle) t ∧ StackProps.regBound handler k →
            ∃ clock postTarget, clock ≤ resultBudget r ∧
              evaluate (comp j off k handler, {t with clock := clock + t.clock}) = (r, postTarget) ∧
              (match r with
               | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
               | _ => stateRelHOL j off k post postTarget)
      | _, _ => True)
    (hypothesis : evaluate (.call ret dest handler, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.call ret dest handler : HolProg width) pointer) :
    ∃ clock postTarget, clock ≤ resultBudget result ∧
      evaluate (comp jump bounds pointer (.call ret dest handler),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  cases ret with
  | none =>
    obtain ⟨clock, postTarget, small, run, relation⟩ :=
      InitECandidate.Solver.StackRemoveBound.compCorrectCallTail dest handler source result postSource target
        pointer bounds jump calleeIH hypothesis
    refine ⟨clock, postTarget, small, run, ?_⟩
    cases result with
    | none => exact relation
    | some value => cases value <;> exact relation
  | some returning =>
    rcases returning with ⟨body, link, l1, l2⟩
    cases handler with
    | none =>
      obtain ⟨clock, postTarget, small, run, relation⟩ :=
        InitECandidate.Solver.StackRemoveBound.compCorrectCallReturnNone body link l1 l2 dest source result
          postSource target pointer bounds jump calleeIH returnIH hypothesis
      refine ⟨clock, postTarget, small, run, ?_⟩
      cases result with
      | none => exact relation
      | some value => cases value <;> exact relation
    | some exceptional =>
      rcases exceptional with ⟨handlerBody, hl1, hl2⟩
      obtain ⟨clock, postTarget, small, run, relation⟩ :=
        InitECandidate.Solver.StackRemoveBound.compCorrectCallReturnHandler body handlerBody link l1 l2 hl1 hl2
          dest source result postSource target pointer bounds jump calleeIH returnIH handlerIH hypothesis
      refine ⟨clock, postTarget, small, run, ?_⟩
      cases result with
      | none => exact relation
      | some value => cases value <;> exact relation

end InitECandidate.Solver.StackRemoveBound
#print axioms InitECandidate.Solver.StackRemoveBound.compCorrectCall
