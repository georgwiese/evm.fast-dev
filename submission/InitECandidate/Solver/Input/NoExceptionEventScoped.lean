import InitECandidate.Solver.Input.NoExceptionEvent

namespace InitECandidate.Solver.Input.NoExceptionEvent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem scoped_body (code) (identifier : MlS) (payload : ValueHOL 64)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (entry : code.lookup function = some (formals, body, returnShape))
    (calleeSafe : Safe code identifier payload body) (tailSafe : Safe code identifier payload continuation) :
    Safe code identifier payload (.decCall (ofString name) shape function arguments continuation) := by
  intro source installed impossible
  let post := (evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation)).2
  have run : evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation) = (some (.exception identifier payload), post) := Prod.ext impossible rfl
  obtain ⟨positive, values, actual, callee, actualShape, target, args, called, cases⟩ :=
    CallNormal.scoped_exception_data source post name shape function arguments continuation identifier payload run
  have lookup : lookupCodeHOLFinite code.lookup function values = some (actual, callee, actualShape) := by rw [← installed]; exact called
  have bodyEq := LocalEffects.lookup_body code function formals body returnShape entry values actual callee actualShape lookup
  rcases cases with escaped | continued
  · obtain ⟨bodyRun, postEq⟩ := escaped
    rw [bodyEq] at bodyRun
    have excluded := calleeSafe (callEntryStateHOLFinite source callee) installed
    rw [bodyRun] at excluded
    exact excluded rfl
  · obtain ⟨returned, inner, bodyRun, checked, tailRun, postEq⟩ := continued
    have targetCode := (evaluation_fields (callEntryStateHOLFinite source callee) target actual (some (.returned returned)) bodyRun).2.2.2
    have nextCode : (CallNormal.continuationEntry source target name returned).code = code := targetCode.trans installed
    have excluded := tailSafe (CallNormal.continuationEntry source target name returned) nextCode
    rw [tailRun] at excluded
    exact excluded rfl

end InitECandidate.Solver.Input.NoExceptionEvent

#print axioms InitECandidate.Solver.Input.NoExceptionEvent.scoped_body
