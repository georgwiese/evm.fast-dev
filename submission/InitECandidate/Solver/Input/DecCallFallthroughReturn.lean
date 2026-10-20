import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem continuation_congr {F : Type} (source : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (left right : ProgHOL 64)
    (same : ∀ state : PanSemStateFiniteExact 64 F,evaluateHOLFiniteState state left = evaluateHOLFiniteState state right) :
    evaluateHOLFiniteState source (.decCall name shape function arguments left) = evaluateHOLFiniteState source (.decCall name shape function arguments right) := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite,evaluateHOLFiniteState_decCall_fixClockRewrite]
  simp_rw [same]

/-- A real fall-through scoped call can append a constant return inside its
scope. This exposes its reached continuation to the normal-return contracts. -/
theorem fallthrough_return {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation) = (none,post)) :
    evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments (.seq continuation (.return (.const 0#64)))) = (some (.returned (.val (.word 0#64))),restore source name (emptyLocalsHOLFinite post)) := by
  classical
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at normal ⊢
  cases args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments with
  | none => simp only [args] at normal; cases normal
  | some values =>
    simp only [args] at normal ⊢
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called] at normal; cases normal
    | some data =>
      obtain ⟨body,callee,returnShape⟩ := data
      simp only [called] at normal ⊢
      by_cases zero : source.clock = 0
      · rw [if_pos zero] at normal; cases normal
      · rw [if_neg zero] at normal ⊢
        generalize bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = answer at normal ⊢
        obtain ⟨result,target⟩ := answer
        cases result with
        | none => cases normal
        | some result =>
          cases result with
          | returned value =>
            simp only at normal ⊢
            by_cases valid : (shapeEqHOL (shapeOfHOLExact value) shape && shapeEqHOL (shapeOfHOLExact value) returnShape) = true
            · rw [if_pos valid] at normal ⊢
              change (let output := evaluateHOLFiniteState (continuationEntry source target name value) continuation; (output.1,restore source name output.2)) = (none,post) at normal
              change (let output := evaluateHOLFiniteState (continuationEntry source target name value) (.seq continuation (.return (.const 0#64))); (output.1,restore source name output.2)) = _
              generalize continuationRun : evaluateHOLFiniteState (continuationEntry source target name value) continuation = output at normal
              obtain ⟨outcome,inner⟩ := output
              change (outcome,restore source name inner) = (none,post) at normal
              have pair := Prod.mk.inj normal
              cases pair.1
              rw [evaluateHOLFiniteState_seq_line780]
              change evaluateHOLFiniteState (continuationEntry source target name value) continuation = (none,inner) at continuationRun
              rw [continuationRun]
              simpa [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL,sizeOfShapeHOL,restore,emptyLocalsHOLFinite] using congrArg (fun s => (some (PanSemResultExact.returned (.val (.word 0#64))),restore source name (emptyLocalsHOLFinite s))) pair.2
            · rw [if_neg valid] at normal; cases normal
          | error => cases normal
          | timeOut => cases normal
          | «break» => cases normal
          | «continue» => cases normal
          | exception identifier payload => cases normal
          | finalFfi event => cases normal

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.fallthrough_return

#print axioms InitECandidate.Solver.Input.CallNormal.continuation_congr
