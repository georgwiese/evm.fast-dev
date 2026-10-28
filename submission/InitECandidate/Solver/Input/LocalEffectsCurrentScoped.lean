import InitECandidate.Solver.Input.LocalEffectsScoped

namespace InitECandidate.Solver.Input.LocalEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Transport a full nonlocal frame from the concrete callee entry of the
same actual call. Its supplied operands may establish stronger facts than
an arbitrary state's bindings, without assuming a successful call. -/
theorem scoped_current (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,returnShape))
    (frame : erase (evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).2=erase source)
    (tail : Preserves source.code continuation) :
    erase (evaluateHOLFiniteState source (.decCall name shape function arguments continuation)).2=erase source := by
  classical
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  simp only [args,called]
  by_cases zero : source.clock=0
  · rw [if_pos zero]; rfl
  · rw [if_neg zero]
    generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output at frame ⊢
    obtain ⟨result,target⟩:=output
    cases result with
    | none=>exact frame
    | some result=>
      cases result with
      | returned value=>
        simp only
        split
        · have codeEq : target.code=source.code := code_of_erase source target frame
          have next:=tail (setVarHOLFinite name value {target with locals:=source.locals}) codeEq
          exact next.trans frame
        · exact frame
      | error | timeOut | «break» | «continue» | exception identifier value | finalFfi event=>exact frame

end InitECandidate.Solver.Input.LocalEffects

#print axioms InitECandidate.Solver.Input.LocalEffects.scoped_current
