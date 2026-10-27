import InitECandidate.Solver.Input.NormalHeapLoop
import InitECandidate.Solver.Input.NormalHostCall
import InitECandidate.Solver.Input.GlobalEffectsCall

namespace InitECandidate.Solver.Input.NormalHeapEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

abbrev callInfo := NormalHostEffects.callInfo

/-- A call result may change any local or another global, but must not
replace the allocator cursor independently of its checked body contract. -/
def Safe : Option (Option (VarKind × MlS)) → Prop
  | some (some (.global, name)) => ofString "heap_ptr" ≠ name
  | _ => True

theorem update_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower : Nat) (name : MlS) (value : ValueHOL 64)
    (other : ofString "heap_ptr" ≠ name) (initial : AtLeast lower source) :
    AtLeast lower (setGlobalHOLFinite name value source) := by
  obtain ⟨pointer, cell, lowerBound, upperBound, aligned⟩ := initial
  refine ⟨pointer, ?_, lowerBound, upperBound, aligned⟩
  simpa [setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE, Ne.symm other] using cell

/-- A real returned body carries the current heap frontier through an
ordinary tail/ignored/local/other-global call. Callee failure is unrestricted. -/
theorem called (code) (destination : Option (Option (VarKind × MlS))) (function : MlS) (arguments : List (ExpHOL 64))
    (safe : Safe destination)
    (calleePure : ∀ values body callee shape, lookupCodeHOLFinite code.lookup function values = some (body, callee, shape) → Returning code body) :
    Preserves code (.call (callInfo destination) function arguments) := by
  classical
  intro source installed lower initial resumes
  rw [evaluateHOLFiniteState_call] at resumes ⊢
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args]; exact initial
  | some values =>
    simp only [args] at resumes ⊢
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called]; exact initial
    | some data =>
      obtain ⟨body, callee, shape⟩ := data
      simp only [called] at resumes ⊢
      by_cases zero : source.clock = 0
      · rw [if_pos zero]; exact initial
      · rw [if_neg zero] at resumes ⊢
        have lookup : lookupCodeHOLFinite code.lookup function values = some (body, callee, shape) := by rw [← installed]; exact called
        have frame := calleePure values body callee shape lookup (callEntryStateHOLFinite source callee) installed lower initial
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at frame resumes ⊢
        obtain ⟨result, target⟩ := output
        cases result with
        | none => cases destination <;> simp [callInfo, NormalHostEffects.callInfo, NormalHostEffects.Resumes] at resumes
        | some result =>
          cases result with
          | returned value =>
            have bodyHeap : AtLeast lower target := frame value rfl
            cases destination with
            | none =>
              simp only [callInfo, NormalHostEffects.callInfo, Option.map_none]
              split <;> exact bodyHeap
            | some destination =>
              simp only [callInfo, NormalHostEffects.callInfo, Option.map_some]
              split
              · cases destination with
                | none => exact bodyHeap
                | some data =>
                  obtain ⟨kind, name⟩ := data
                  simp only
                  split
                  · cases kind with
                    | «local» => exact bodyHeap
                    | «global» => exact update_other {target with locals := source.locals} lower name value safe bodyHeap
                  · exact bodyHeap
              · exact bodyHeap
          | error | timeOut | «break» | «continue» | exception identifier payload | finalFfi event =>
            cases destination <;> simp [callInfo, NormalHostEffects.callInfo, NormalHostEffects.Resumes] at resumes

theorem call_body (code) (destination : Option (Option (VarKind × MlS))) (function : MlS) (arguments : List (ExpHOL 64))
    (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL)
    (entry : code.lookup function = some (formals, body, shape)) (pureBody : Returning code body) (safe : Safe destination) :
    Preserves code (.call (callInfo destination) function arguments) := by
  apply called code destination function arguments safe
  intro values actual callee returnShape lookedUp
  rw [GlobalEffects.lookup_body code function formals body shape entry values actual callee returnShape lookedUp]
  exact pureBody

theorem scoped_body (code) (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (entry : code.lookup function = some (formals, body, returnShape))
    (pureBody : Returning code body) (pureContinuation : Preserves code continuation) :
    Preserves code (.decCall name shape function arguments continuation) := by
  classical
  intro source installed lower initial resumes
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at resumes ⊢
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args]; exact initial
  | some values =>
    simp only [args] at resumes ⊢
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called]; exact initial
    | some data =>
      obtain ⟨actual, callee, actualShape⟩ := data
      simp only [called] at resumes ⊢
      by_cases zero : source.clock = 0
      · rw [if_pos zero]; exact initial
      · rw [if_neg zero] at resumes ⊢
        have lookup : lookupCodeHOLFinite code.lookup function values = some (actual, callee, actualShape) := by rw [← installed]; exact called
        have bodyEq := GlobalEffects.lookup_body code function formals body returnShape entry values actual callee actualShape lookup
        subst actual
        have frame := pureBody (callEntryStateHOLFinite source callee) installed lower initial
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at frame resumes ⊢
        obtain ⟨result, target⟩ := output
        cases result with
        | none => simp [NormalHostEffects.Resumes] at resumes
        | some result =>
          cases result with
          | returned value =>
            have bodyHeap : AtLeast lower target := frame value rfl
            simp only at resumes ⊢
            by_cases checked : (shapeEqHOL (shapeOfHOLExact value) shape &&
                shapeEqHOL (shapeOfHOLExact value) actualShape) = true
            · rw [if_pos checked] at resumes ⊢
              have fields := evaluation_fields (callEntryStateHOLFinite source callee) target body (some (.returned value)) computed
              exact pureContinuation (setVarHOLFinite name value {target with locals := source.locals})
                (fields.2.2.2.trans installed) lower bodyHeap resumes
            · rw [if_neg checked]; exact bodyHeap
          | error | timeOut | «break» | «continue» | exception identifier payload | finalFfi event =>
            simp [NormalHostEffects.Resumes] at resumes

end InitECandidate.Solver.Input.NormalHeapEffects

#print axioms InitECandidate.Solver.Input.NormalHeapEffects.update_other
#print axioms InitECandidate.Solver.Input.NormalHeapEffects.called
#print axioms InitECandidate.Solver.Input.NormalHeapEffects.call_body
#print axioms InitECandidate.Solver.Input.NormalHeapEffects.scoped_body
