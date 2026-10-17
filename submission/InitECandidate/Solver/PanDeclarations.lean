import InitECandidate.Solver.PanState

/-! Actual local declarations and restoration for arbitrary Pancake programs.
This execution interface is independent of the retired replacement helper. -/
namespace InitECandidate.Solver.WitnessRadix.BuildEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

def returnZero : ProgHOL 64 := .return (.const 0#64)
theorem zero_return {F : Type} (source : PanSemStateFiniteExact 64 F) :
    evaluateHOLFiniteState source returnZero =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite source) := by
  classical
  simp [returnZero, evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]


def declarations : List (String × ExpHOL 64) → ProgHOL 64 → ProgHOL 64
  | [], continuation => continuation
  | (name, expression) :: rest, continuation =>
      .dec (ofString name) .one expression (declarations rest continuation)

/-- Entry prefix evidence consists only of actual expression evaluations.
It records all lexical restorations needed after the body returns. -/
inductive Initializes {F : Type} : PanSemStateFiniteExact 64 F → List (String × ExpHOL 64) →
    PanSemStateFiniteExact 64 F → (PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F) → Prop
  | done (source) : Initializes source [] source id
  | step {source entered name expression rest restoreRest} (word : BitVec 64)
      (read : eval source expression = some (.val (.word word)))
      (next : Initializes (bind source name word) rest entered restoreRest) :
      Initializes source ((name, expression) :: rest) entered
        (fun output => restore source name (restoreRest output))

theorem declarations_execute {F : Type} {source entered : PanSemStateFiniteExact 64 F}
    {bindings : List (String × ExpHOL 64)}
    {restoreStack : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F}
    (setup : Initializes source bindings entered restoreStack) (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (declarations bindings continuation) =
      (let output := evaluateHOLFiniteState entered continuation;
       (output.1, restoreStack output.2)) := by
  classical
  induction setup with
  | done source => rfl
  | @step source entered name expression rest restoreRest word read next ih =>
      simp only [eval] at read
      rw [declarations, evaluateHOLFiniteState_dec_total]
      simp only [read, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
      change (let output := evaluateHOLFiniteState (bind source name word) (declarations rest continuation);
        (output.1, restore source name output.2)) = _
      rw [ih]

theorem initialization_frame {F : Type} {source entered : PanSemStateFiniteExact 64 F}
    {bindings : List (String × ExpHOL 64)}
    {restoreStack : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F}
    (setup : Initializes source bindings entered restoreStack) :
    emptyLocalsHOLFinite entered = emptyLocalsHOLFinite source := by
  induction setup with
  | done source => rfl
  | step word read next ih => exact ih

theorem restoration_frame {F : Type} {source entered : PanSemStateFiniteExact 64 F}
    {bindings : List (String × ExpHOL 64)}
    {restoreStack : PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F}
    (setup : Initializes source bindings entered restoreStack) (output : PanSemStateFiniteExact 64 F) :
    emptyLocalsHOLFinite (restoreStack output) = emptyLocalsHOLFinite output := by
  induction setup with
  | done source => rfl
  | step word read next ih => exact ih

end InitECandidate.Solver.WitnessRadix.BuildEntry

#print axioms InitECandidate.Solver.WitnessRadix.BuildEntry.declarations_execute
#print axioms InitECandidate.Solver.WitnessRadix.BuildEntry.initialization_frame
#print axioms InitECandidate.Solver.WitnessRadix.BuildEntry.restoration_frame

#print axioms InitECandidate.Solver.WitnessRadix.BuildEntry.zero_return
