import InitECandidate.Solver.Input.NoNamedException

namespace InitECandidate.Solver.Input.NoExceptionEvent
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def Safe (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (identifier : MlS) (payload : ValueHOL 64) (program : ProgHOL 64) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory, source.code = code →
    (evaluateHOLFiniteState source program).1 ≠ some (.exception identifier payload)

theorem of_all (code) (identifier : MlS) (payload : ValueHOL 64) (program : ProgHOL 64)
    (safe : NoException.Safe code program) : Safe code identifier payload program := by
  intro source installed
  exact safe source installed identifier payload

theorem of_named (code) (identifier : MlS) (payload : ValueHOL 64) (program : ProgHOL 64)
    (safe : NoNamedException.Safe code identifier program) : Safe code identifier payload program := by
  intro source installed
  exact safe source installed payload

theorem raise_literal (code) (identifier actual : MlS) (payload : ValueHOL 64) (word : BitVec 64)
    (other : .val (.word word) ≠ payload) : Safe code identifier payload (.raise actual (.const word)) := by
  intro source installed
  rw [evaluateHOLFiniteState_raise]
  simp only [evalHOLExact]
  repeat first | (solve | simp_all [other]) | split

theorem sequence (code) (identifier : MlS) (payload : ValueHOL 64) (first second : ProgHOL 64)
    (front : Safe code identifier payload first) (back : Safe code identifier payload second) : Safe code identifier payload (.seq first second) := by
  intro source installed
  have firstSafe := front source installed
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first = output at firstSafe ⊢
  obtain ⟨result, middle⟩ := output
  cases result with
  | none =>
    have fields := evaluation_fields source middle first none computed
    exact back middle (fields.2.2.2.trans installed)
  | some result => exact firstSafe

theorem declared (code) (identifier name : MlS) (payload : ValueHOL 64)
    (shape : ShapeHOL) (expression : ExpHOL 64) (body : ProgHOL 64) (safe : Safe code identifier payload body) :
    Safe code identifier payload (.dec name shape expression body) := by
  intro source installed
  rw [evaluateHOLFiniteState_dec_total]
  simp only
  split
  · simp
  · rename_i value read
    split
    · exact safe (setVarHOLFinite name value source) installed
    · simp

theorem conditional (code) (identifier : MlS) (payload : ValueHOL 64) (test : ExpHOL 64) (yes no : ProgHOL 64)
    (left : Safe code identifier payload yes) (right : Safe code identifier payload no) : Safe code identifier payload (.ite test yes no) := by
  intro source installed
  rw [evaluateHOLFiniteState_ite]
  repeat first | exact left source installed | exact right source installed | (solve | simp) | split

theorem call_body (code) (identifier function : MlS) (payload : ValueHOL 64) (arguments : List (ExpHOL 64))
    (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL)
    (entry : code.lookup function = some (formals, body, shape)) (safe : Safe code identifier payload body) :
    Safe code identifier payload (.call (some (none, none)) function arguments) := by
  intro source installed impossible
  let post := (evaluateHOLFiniteState source (.call (some (none, none)) function arguments)).2
  have run : evaluateHOLFiniteState source (.call (some (none, none)) function arguments) = (some (.exception identifier payload), post) := Prod.ext impossible rfl
  obtain ⟨positive, values, actual, callee, returnShape, target, args, called, bodyRun, postEq, fields⟩ :=
    CallNormal.ignored_exception_data source post function arguments identifier payload run
  have lookup : lookupCodeHOLFinite code.lookup function values = some (actual, callee, returnShape) := by rw [← installed]; exact called
  have bodyEq := LocalEffects.lookup_body code function formals body shape entry values actual callee returnShape lookup
  rw [bodyEq] at bodyRun
  have excluded := safe (callEntryStateHOLFinite source callee) installed
  rw [bodyRun] at excluded
  exact excluded rfl

end InitECandidate.Solver.Input.NoExceptionEvent

#print axioms InitECandidate.Solver.Input.NoExceptionEvent.raise_literal
#print axioms InitECandidate.Solver.Input.NoExceptionEvent.sequence
#print axioms InitECandidate.Solver.Input.NoExceptionEvent.declared
#print axioms InitECandidate.Solver.Input.NoExceptionEvent.conditional
#print axioms InitECandidate.Solver.Input.NoExceptionEvent.call_body
