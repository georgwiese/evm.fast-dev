import InitECandidate.Solver.Input.ClockCostCall

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem scoped_call (code) (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (calleePrice continuationPrice : Nat)
    (calleeBound : ∀ values body callee returnShape, lookupCodeHOLFinite code.lookup function values = some (body, callee, returnShape) → Bound code body calleePrice)
    (continuationBound : Bound code continuation continuationPrice) :
    Bound code (.decCall name shape function arguments continuation) (calleePrice + continuationPrice + 1) := by
  classical
  intro source installed
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args]; omega
  | some values =>
    simp only [args]
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called]; omega
    | some data =>
      obtain ⟨body, callee, returnShape⟩ := data
      simp only [called]
      by_cases zero : source.clock = 0
      · rw [if_pos zero]; change source.clock - source.clock ≤ _; omega
      · rw [if_neg zero]
        have lookup : lookupCodeHOLFinite code.lookup function values = some (body, callee, returnShape) := by rw [← installed]; exact called
        have bodyCost := calleeBound values body callee returnShape lookup (callEntryStateHOLFinite source callee) installed
        have bodyClock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at bodyCost bodyClock ⊢
        obtain ⟨result, target⟩ := output
        have cost : source.clock - target.clock ≤ calleePrice + continuationPrice + 1 := by
          change source.clock - 1 - target.clock ≤ calleePrice at bodyCost
          change target.clock ≤ source.clock - 1 at bodyClock
          omega
        cases result with
        | none => exact cost
        | some result =>
          cases result with
          | returned returned =>
            simp only
            split
            · have targetCode := (Input.evaluation_fields (callEntryStateHOLFinite source callee) target body (some (.returned returned)) computed).2.2.2
              have codeEq : target.code = code := targetCode.trans installed
              let ready := setVarHOLFinite name returned {target with locals := source.locals}
              have tailCost := continuationBound ready codeEq
              have tailClock := evaluateHOLFiniteState_clock_le ready continuation
              change target.clock - (evaluateHOLFiniteState ready continuation).2.clock ≤ continuationPrice at tailCost
              change (evaluateHOLFiniteState ready continuation).2.clock ≤ target.clock at tailClock
              change source.clock - (evaluateHOLFiniteState ready continuation).2.clock ≤ _
              change source.clock - 1 - target.clock ≤ calleePrice at bodyCost
              change target.clock ≤ source.clock - 1 at bodyClock
              omega
            · exact cost
          | error => exact cost
          | timeOut => exact cost
          | «break» => exact cost
          | «continue» => exact cost
          | exception identifier payload => exact cost
          | finalFfi event => exact cost

theorem scoped_body (code) (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (calleePrice continuationPrice : Nat)
    (entry : code.lookup function = some (formals, body, returnShape))
    (calleeBound : Bound code body calleePrice) (continuationBound : Bound code continuation continuationPrice) :
    Bound code (.decCall name shape function arguments continuation) (calleePrice + continuationPrice + 1) := by
  apply scoped_call
  · intro values actual callee actualShape lookedUp
    rw [LocalEffects.lookup_body code function formals body returnShape entry values actual callee actualShape lookedUp]
    exact calleeBound
  · exact continuationBound

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.scoped_call
#print axioms InitECandidate.Solver.Input.ClockCost.scoped_body
