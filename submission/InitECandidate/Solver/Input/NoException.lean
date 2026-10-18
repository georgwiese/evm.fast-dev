import InitECandidate.Solver.Input.EvaluationFields

namespace InitECandidate.Solver.Input.NoException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Exclude source exceptions at every clock/outcome; errors, timeout,
returns and final FFI are retained. This is not a totality or cost claim. -/
def Safe (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (program : ProgHOL 64) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory, source.code = code → ∀ identifier payload,
    (evaluateHOLFiniteState source program).1 ≠ some (.exception identifier payload)

theorem skip (code) : Safe code .skip := by
  intro source installed identifier payload
  rw [evaluateHOLFiniteState_skip]
  simp

theorem returned (code) (expression : ExpHOL 64) : Safe code (.return expression) := by
  intro source installed identifier payload
  rw [evaluateHOLFiniteState_return]
  split
  · simp
  · split <;> simp

theorem store (code) (address value : ExpHOL 64) : Safe code (.store address value) := by
  intro source installed identifier payload
  rw [evaluateHOLFiniteState_store]
  repeat first | (solve | simp) | split

theorem assign (code) (name : MlS) (expression : ExpHOL 64) : Safe code (.assign .local name expression) := by
  intro source installed identifier payload
  rw [evaluateHOLFiniteState_assign]
  repeat first | (solve | simp) | split

theorem sequence (code) (first second : ProgHOL 64) (front : Safe code first) (back : Safe code second) :
    Safe code (.seq first second) := by
  intro source installed identifier payload
  have firstSafe := front source installed identifier payload
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first = output at firstSafe ⊢
  obtain ⟨result, middle⟩ := output
  cases result with
  | none =>
      have fields := evaluation_fields source middle first none computed
      exact back middle (fields.2.2.2.trans installed) identifier payload
  | some result => exact firstSafe

theorem declared (code) (name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) (body : ProgHOL 64)
    (safe : Safe code body) : Safe code (.dec name shape expression body) := by
  intro source installed identifier payload
  rw [evaluateHOLFiniteState_dec_total]
  simp only
  split
  · simp
  · rename_i value read
    split
    · exact safe (setVarHOLFinite name value source) installed identifier payload
    · simp

theorem conditional (code) (test : ExpHOL 64) (yes no : ProgHOL 64) (left : Safe code yes) (right : Safe code no) :
    Safe code (.ite test yes no) := by
  intro source installed identifier payload
  rw [evaluateHOLFiniteState_ite]
  repeat first | exact left source installed identifier payload | exact right source installed identifier payload | (solve | simp) | split

end InitECandidate.Solver.Input.NoException

#print axioms InitECandidate.Solver.Input.NoException.sequence
#print axioms InitECandidate.Solver.Input.NoException.declared
#print axioms InitECandidate.Solver.Input.NoException.conditional
#print axioms InitECandidate.Solver.Input.NoException.store
#print axioms InitECandidate.Solver.Input.NoException.returned
