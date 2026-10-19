import InitECandidate.Solver.Input.GlobalEffectsLoop

namespace InitECandidate.Solver.Input.GlobalEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def callInfo (destination : Option (Option MlS)) :
    Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)) :=
  destination.map (fun name => (name.map (fun name => (.local, name)), none))

/-- Tail calls, ignored calls and local-result calls preserve the selected
global and code when their real looked-up bodies do. Failed lookup/shape/assignment,
exceptions and timeout are covered; no callee success premise is imposed. -/
theorem called (key : MlS) (code) (destination : Option (Option MlS)) (function : MlS) (arguments : List (ExpHOL 64))
    (calleePure : ∀ values body callee shape, lookupCodeHOLFinite code.lookup function values = some (body, callee, shape) → Preserves key code body) :
    Preserves key code (.call (callInfo destination) function arguments) := by
  classical
  intro source installed
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
        have frame := calleePure values body callee shape lookup (callEntryStateHOLFinite source callee) installed
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at frame ⊢
        obtain ⟨result, target⟩ := output
        have postFrame : erase key target = erase key source := frame
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

/-- A checked ordinary code entry identifies every successfully looked-up
body, regardless of actual argument values or formal-shape failure. -/
theorem lookup_body (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (function : MlS) (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL)
    (entry : code.lookup function = some (formals, body, shape))
    (values : List (ValueHOL 64)) (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (lookedUp : lookupCodeHOLFinite code.lookup function values = some (actual, callee, returnShape)) : actual = body := by
  have raw := lookupCodeHOLFinite_eq_some code.lookup function values actual callee returnShape lookedUp
  simp only [lookupCodeHOLExact, entry] at raw
  split at raw
  · exact (congrArg Prod.fst (Option.some.inj raw)).symm
  · cases raw

theorem call_body (key : MlS) (code) (destination : Option (Option MlS)) (function : MlS) (arguments : List (ExpHOL 64))
    (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL)
    (entry : code.lookup function = some (formals, body, shape)) (pureBody : Preserves key code body) :
    Preserves key code (.call (callInfo destination) function arguments) := by
  apply called
  intro values actual callee returnShape lookedUp
  rw [lookup_body code function formals body shape entry values actual callee returnShape lookedUp]
  exact pureBody

end InitECandidate.Solver.Input.GlobalEffects

#print axioms InitECandidate.Solver.Input.GlobalEffects.called
#print axioms InitECandidate.Solver.Input.GlobalEffects.lookup_body
#print axioms InitECandidate.Solver.Input.GlobalEffects.call_body
