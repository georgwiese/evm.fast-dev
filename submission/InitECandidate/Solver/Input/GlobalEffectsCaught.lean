import InitECandidate.Solver.Input.GlobalEffectsScoped

namespace InitECandidate.Solver.Input.GlobalEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- The selected global is preserved through every result of a genuine
caught ignored call, including its actual handler execution. -/
theorem caught_destination (key : MlS) (code) (destination : Option MlS) (function : MlS) (arguments : List (ExpHOL 64))
    (formals : List (MlS×ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL)
    (identifier parameter : MlS) (handler : ProgHOL 64)
    (entry : code.lookup function=some (formals,body,shape))
    (pureBody : Preserves key code body) (pureHandler : Preserves key code handler) :
    Preserves key code (.call (some (destination.map (fun name=>(.local,name)),some (identifier,parameter,handler))) function arguments) := by
  intro source installed
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args]
  | some values =>
    simp only [args]
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called]
    | some data =>
      obtain ⟨actualBody,callee,actualShape⟩ := data
      simp only [called]
      have lookedUp : lookupCodeHOLFinite code.lookup function values=some (actualBody,callee,actualShape) := by rw [←installed]; exact called
      have bodyEq := lookup_body code function formals body shape entry values actualBody callee actualShape lookedUp
      by_cases zero : source.clock=0
      · rw [if_pos zero]; rfl
      · rw [if_neg zero]
        have pureActual : Preserves key code actualBody := by rw [bodyEq]; exact pureBody
        have frame := pureActual (callEntryStateHOLFinite source callee) installed
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) actualBody=output at frame ⊢
        obtain ⟨result,target⟩ := output
        have postFrame : erase key target=erase key source := frame
        cases result with
        | none => exact postFrame
        | some result =>
          cases result with
          | returned value =>
            simp only
            split
            · cases destination with
              | none => exact postFrame
              | some name => simp only [Option.map_some]; split <;> exact postFrame
            · exact postFrame
          | exception exceptionId value =>
            simp only
            split
            · split
              · split
                · have codeEq : target.code=code := (code_of_erase key source target postFrame).trans installed
                  have handlerFrame := pureHandler (setVarHOLFinite parameter value {target with locals:=source.locals}) codeEq
                  exact handlerFrame.trans postFrame
                · exact postFrame
              · exact postFrame
            · exact postFrame
          | error => exact postFrame
          | timeOut => exact postFrame
          | «break» => exact postFrame
          | «continue» => exact postFrame
          | finalFfi event => exact postFrame

/-- Ignored-result specialization of the shared caught-call effect rule. -/
theorem caught_body (key : MlS) (code) (function : MlS) (arguments : List (ExpHOL 64))
    (formals : List (MlS×ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL)
    (identifier parameter : MlS) (handler : ProgHOL 64)
    (entry : code.lookup function=some (formals,body,shape))
    (pureBody : Preserves key code body) (pureHandler : Preserves key code handler) :
    Preserves key code (.call (some (none,some (identifier,parameter,handler))) function arguments) :=
  caught_destination key code none function arguments formals body shape identifier parameter handler entry pureBody pureHandler

end InitECandidate.Solver.Input.GlobalEffects

#print axioms InitECandidate.Solver.Input.GlobalEffects.caught_body

#print axioms InitECandidate.Solver.Input.GlobalEffects.caught_destination
