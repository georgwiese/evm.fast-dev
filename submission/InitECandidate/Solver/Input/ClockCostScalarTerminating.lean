import InitECandidate.Solver.Input.ClockCostScopeLocals
import InitECandidate.Solver.Input.ClockCostTerminatingScoped

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Scalar scope composition restricted only by the same observed non-timeout
parent outcome. Continuation facts derive from the actual checked callee return;
failed arguments/lookups, traps and errors remain in scope. -/
theorem scalar_scope_terminating (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (function : MlS)
    (arguments : List (ExpHOL 64)) (formals : List (MlS × ShapeHOL)) (body continuation : ProgHOL 64)
    (returnShape : ShapeHOL) (calleePrice tailPrice : Nat)
    (code : source.code.lookup function = some (formals, body, returnShape))
    (priced : Bound source.code body calleePrice)
    (tail : ∀ target : PanSemStateFiniteExact 64 Guest.HostMemory, ∀ word : BitVec 64, target.code = source.code →
      ∀ result final, evaluateHOLFiniteState (CallNormal.continuationEntry source target name (.val (.word word))) continuation = (result, final) →
        result ≠ some .timeOut → target.clock - final.clock ≤ tailPrice)
    (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (.decCall (ofString name) .one function arguments continuation) = (result, post))
    (notTimeout : result ≠ some .timeOut) : source.clock - post.clock ≤ calleePrice + tailPrice + 1 := by
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none =>
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite, args] at actual
    have clock := congrArg (fun output => output.2.clock) actual
    dsimp only at clock
    omega
  | some values =>
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none =>
      rw [evaluateHOLFiniteState_decCall_fixClockRewrite, args] at actual
      simp only [called] at actual
      have clock := congrArg (fun output => output.2.clock) actual
      dsimp only at clock
      omega
    | some data =>
      obtain ⟨actualBody, callee, shape⟩ := data
      have same := LocalEffects.lookup_body source.code function formals body returnShape code values actualBody callee shape called
      subst actualBody
      apply scoped_reached_terminating source post name .one function arguments values body continuation callee shape calleePrice tailPrice args called
        (by intro result target evaluated notTimeout
            have price := priced (callEntryStateHOLFinite source callee) rfl
            rw [evaluated] at price
            exact price) ?_ result actual notTimeout
      intro target value returned checked
      have typed : shapeOfHOLExact value = .one := (shapeEqHOL_eq_true _ _).mp (Bool.and_eq_true_iff.mp checked).1
      obtain ⟨word, rfl⟩ := ScalarShape.word value typed
      exact tail target word ((evaluation_fields (callEntryStateHOLFinite source callee) target body _ returned).2.2.2)

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.scalar_scope_terminating
