import InitECandidate.Solver.Input.NoExceptionScoped
import InitECandidate.Solver.Input.IgnoredCallException

namespace InitECandidate.Solver.Input.NoNamedException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exclude one source exception name while retaining all other outcomes,
including other exceptions and externally stopping traps. -/
def Safe (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (forbidden : MlS) (program : ProgHOL 64) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory, source.code = code → ∀ payload,
    (evaluateHOLFiniteState source program).1 ≠ some (.exception forbidden payload)

theorem of_all (code) (forbidden : MlS) (program : ProgHOL 64) (safe : NoException.Safe code program) : Safe code forbidden program := by
  intro source installed payload
  exact safe source installed forbidden payload

theorem raised_other (code) (forbidden actual : MlS) (expression : ExpHOL 64) (other : actual ≠ forbidden) :
    Safe code forbidden (.raise actual expression) := by
  intro source installed payload
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split <;> simp [other]
  · simp

theorem sequence (code) (forbidden : MlS) (first second : ProgHOL 64)
    (front : Safe code forbidden first) (back : Safe code forbidden second) : Safe code forbidden (.seq first second) := by
  intro source installed payload
  have firstSafe := front source installed payload
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first = output at firstSafe ⊢
  obtain ⟨result, middle⟩ := output
  cases result with
  | none =>
    have fields := evaluation_fields source middle first none computed
    exact back middle (fields.2.2.2.trans installed) payload
  | some result => exact firstSafe

theorem declared (code) (forbidden name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) (body : ProgHOL 64)
    (safe : Safe code forbidden body) : Safe code forbidden (.dec name shape expression body) := by
  intro source installed payload
  rw [evaluateHOLFiniteState_dec_total]
  simp only
  split
  · simp
  · rename_i value read
    split
    · exact safe (setVarHOLFinite name value source) installed payload
    · simp

theorem conditional (code) (forbidden : MlS) (test : ExpHOL 64) (yes no : ProgHOL 64)
    (left : Safe code forbidden yes) (right : Safe code forbidden no) : Safe code forbidden (.ite test yes no) := by
  intro source installed payload
  rw [evaluateHOLFiniteState_ite]
  repeat first | exact left source installed payload | exact right source installed payload | (solve | simp) | split

theorem call_body (code) (forbidden function : MlS) (arguments : List (ExpHOL 64))
    (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL)
    (entry : code.lookup function = some (formals, body, shape)) (safe : Safe code forbidden body) :
    Safe code forbidden (.call (some (none, none)) function arguments) := by
  intro source installed payload impossible
  let post := (evaluateHOLFiniteState source (.call (some (none, none)) function arguments)).2
  have run : evaluateHOLFiniteState source (.call (some (none, none)) function arguments) = (some (.exception forbidden payload), post) := Prod.ext impossible rfl
  obtain ⟨positive, values, actual, callee, returnShape, target, args, called, bodyRun, postEq, fields⟩ :=
    CallNormal.ignored_exception_data source post function arguments forbidden payload run
  have lookup : lookupCodeHOLFinite code.lookup function values = some (actual, callee, returnShape) := by rw [← installed]; exact called
  have bodyEq := LocalEffects.lookup_body code function formals body shape entry values actual callee returnShape lookup
  rw [bodyEq] at bodyRun
  have excluded := safe (callEntryStateHOLFinite source callee) installed payload
  rw [bodyRun] at excluded
  exact excluded rfl

theorem scoped_body (code) (forbidden : MlS) (name : String) (shape : ShapeHOL) (function : MlS)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (entry : code.lookup function = some (formals, body, returnShape))
    (calleeSafe : Safe code forbidden body) (tailSafe : Safe code forbidden continuation) :
    Safe code forbidden (.decCall (ofString name) shape function arguments continuation) := by
  intro source installed payload impossible
  let post := (evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation)).2
  have run : evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation) = (some (.exception forbidden payload), post) := Prod.ext impossible rfl
  obtain ⟨positive, values, actual, callee, actualShape, target, args, called, cases⟩ :=
    CallNormal.scoped_exception_data source post name shape function arguments continuation forbidden payload run
  have lookup : lookupCodeHOLFinite code.lookup function values = some (actual, callee, actualShape) := by rw [← installed]; exact called
  have bodyEq := LocalEffects.lookup_body code function formals body returnShape entry values actual callee actualShape lookup
  rcases cases with escaped | continued
  · obtain ⟨bodyRun, postEq⟩ := escaped
    rw [bodyEq] at bodyRun
    have excluded := calleeSafe (callEntryStateHOLFinite source callee) installed payload
    rw [bodyRun] at excluded
    exact excluded rfl
  · obtain ⟨returned, inner, bodyRun, checked, tailRun, postEq⟩ := continued
    have targetCode := (evaluation_fields (callEntryStateHOLFinite source callee) target actual (some (.returned returned)) bodyRun).2.2.2
    have nextCode : (CallNormal.continuationEntry source target name returned).code = code := targetCode.trans installed
    have excluded := tailSafe (CallNormal.continuationEntry source target name returned) nextCode payload
    rw [tailRun] at excluded
    exact excluded rfl

end InitECandidate.Solver.Input.NoNamedException

#print axioms InitECandidate.Solver.Input.NoNamedException.raised_other
#print axioms InitECandidate.Solver.Input.NoNamedException.sequence
#print axioms InitECandidate.Solver.Input.NoNamedException.declared
#print axioms InitECandidate.Solver.Input.NoNamedException.conditional
#print axioms InitECandidate.Solver.Input.NoNamedException.call_body
#print axioms InitECandidate.Solver.Input.NoNamedException.scoped_body
