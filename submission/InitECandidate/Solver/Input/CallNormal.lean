import InitECandidate.Solver.Input.ScalarDeclaration
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Invert a real scoped call with known evaluated arguments/code lookup.
A normal caller return requires an actual callee return; all other callee
outcomes propagate or become errors and cannot enter the continuation. -/
theorem callee_return {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,returnShape))
    (enough : 1≤source.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source (.decCall name shape function arguments continuation)=(some (.returned value),post)) :
    ∃ target returned,evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned returned),target) := by
  classical
  have actual:=evaluateHOLFiniteState_decCall_fixClockRewrite source name shape function arguments continuation
  simp only [args,called,if_neg (show source.clock≠0 from by omega)] at actual
  have normal:=congrArg Prod.fst (actual.symm.trans run)
  generalize outputEq : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output at normal
  obtain ⟨result,target⟩:=output
  cases result with
  | none=>cases normal
  | some result=>
    cases result with
    | returned returned=>exact ⟨target,returned,rfl⟩
    | error=>cases normal
    | timeOut=>cases normal
    | «break»=>cases normal
    | «continue»=>cases normal
    | exception identifier payload=>cases normal
    | finalFfi event=>cases normal

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.callee_return
