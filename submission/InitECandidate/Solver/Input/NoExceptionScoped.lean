import InitECandidate.Solver.Input.NoExceptionCall
import InitECandidate.Solver.Input.ScopedCallException

namespace InitECandidate.Solver.Input.NoException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem primitive (code) (name : MlS) (operator : PrimOp) (arguments : List (ExpHOL 64)) :
    Safe code (.primitive name operator arguments) := by
  intro source installed identifier payload
  rw [evaluateHOLFiniteState_primitive]
  repeat first | simp | split

/-- Nonthrowing original scoped calls, including actual argument/code/shape
failures and every clock. Callee and resumed continuation are both real. -/
theorem scoped_call (code) (name : String) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (calleeSafe : ∀ values body callee returnShape,
      lookupCodeHOLFinite code.lookup function values = some (body, callee, returnShape) → Safe code body)
    (tailSafe : Safe code continuation) :
    Safe code (.decCall (ofString name) shape function arguments continuation) := by
  intro source installed identifier payload impossible
  let post := (evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation)).2
  have run : evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation) = (some (.exception identifier payload), post) :=
    Prod.ext impossible rfl
  obtain ⟨positive, values, body, callee, returnShape, target, args, called, cases⟩ :=
    CallNormal.scoped_exception_data source post name shape function arguments continuation identifier payload run
  have lookup : lookupCodeHOLFinite code.lookup function values = some (body, callee, returnShape) := by rw [← installed]; exact called
  rcases cases with escaped | continued
  · obtain ⟨bodyRun, postEq⟩ := escaped
    have safe := calleeSafe values body callee returnShape lookup (callEntryStateHOLFinite source callee) installed identifier payload
    rw [bodyRun] at safe
    exact safe rfl
  · obtain ⟨returned, inner, bodyRun, checked, tailRun, postEq⟩ := continued
    have targetCode := (Input.evaluation_fields (callEntryStateHOLFinite source callee) target body (some (.returned returned)) bodyRun).2.2.2
    have nextCode : (CallNormal.continuationEntry source target name returned).code = code := targetCode.trans installed
    have safe := tailSafe (CallNormal.continuationEntry source target name returned) nextCode identifier payload
    rw [tailRun] at safe
    exact safe rfl

theorem scoped_body (code) (name : String) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (entry : code.lookup function = some (formals, body, returnShape))
    (calleeSafe : Safe code body) (tailSafe : Safe code continuation) :
    Safe code (.decCall (ofString name) shape function arguments continuation) := by
  apply scoped_call
  · intro values actual callee actualShape called
    rw [LocalEffects.lookup_body code function formals body returnShape entry values actual callee actualShape called]
    exact calleeSafe
  · exact tailSafe

end InitECandidate.Solver.Input.NoException

#print axioms InitECandidate.Solver.Input.NoException.primitive
#print axioms InitECandidate.Solver.Input.NoException.scoped_call
#print axioms InitECandidate.Solver.Input.NoException.scoped_body
