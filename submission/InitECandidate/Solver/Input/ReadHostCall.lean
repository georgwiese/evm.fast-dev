import InitECandidate.Solver.Input.ReadHostLoop
import InitECandidate.Solver.Input.GlobalEffectsCall

namespace InitECandidate.Solver.Input.ReadHostEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def callInfo (destination : Option (Option MlS)) :
    Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)) :=
  destination.map (fun name => (name.map (fun name => (.local, name)), none))

/-- Tail calls, ignored calls and local-result calls preserve host bytes under the fixed source oracle when their real looked-up bodies do. Failed lookup/shape/assignment,
exceptions and timeout are covered; no callee success premise is imposed. -/
theorem called (code) (destination : Option (Option MlS)) (function : MlS) (arguments : List (ExpHOL 64))
    (calleePure : ∀ values body callee shape, lookupCodeHOLFinite code.lookup function values = some (body, callee, shape) → Preserves code body) :
    Preserves code (.call (callInfo destination) function arguments) := by
  classical
  intro source installed oracle
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args]
  | some values =>
    simp only [args]
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called]
    | some data =>
      obtain ⟨body, callee, shape⟩ := data
      simp only [called]
      by_cases zero : source.clock = 0
      · rw [if_pos zero]; rfl
      · rw [if_neg zero]
        have lookup : lookupCodeHOLFinite code.lookup function values = some (body, callee, shape) := by rw [← installed]; exact called
        have frame := calleePure values body callee shape lookup (callEntryStateHOLFinite source callee) installed oracle
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at frame ⊢
        obtain ⟨result, target⟩ := output
        have postFrame : host target = host source := frame
        cases destination with
        | none =>
          cases result with
          | none => exact postFrame
          | some result =>
            cases result <;> simp only [callInfo, Option.map_none]
            all_goals repeat first | exact postFrame | split
        | some destination =>
          cases destination with
          | none =>
            cases result with
            | none => exact postFrame
            | some result =>
              cases result <;> simp only [callInfo, Option.map_some, Option.map_none]
              all_goals repeat first | exact postFrame | split
          | some name =>
            cases result with
            | none => exact postFrame
            | some result =>
              cases result <;> simp only [callInfo, Option.map_some]
              all_goals repeat first | exact postFrame | split

theorem call_body (code) (destination : Option (Option MlS)) (function : MlS) (arguments : List (ExpHOL 64))
    (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL)
    (entry : code.lookup function = some (formals, body, shape)) (pureBody : Preserves code body) :
    Preserves code (.call (callInfo destination) function arguments) := by
  apply called
  intro values actual callee returnShape lookedUp
  rw [GlobalEffects.lookup_body code function formals body shape entry values actual callee returnShape lookedUp]
  exact pureBody

end InitECandidate.Solver.Input.ReadHostEffects

#print axioms InitECandidate.Solver.Input.ReadHostEffects.called
#print axioms InitECandidate.Solver.Input.ReadHostEffects.call_body
