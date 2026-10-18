import InitECandidate.Solver.Input.EvaluationFields

namespace InitECandidate.Solver.Input.QuietClock
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- No source-call/loop clock is spent by these checked finite computations.
This does not count their straight-line target instructions. -/
def Preserves (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (program : ProgHOL 64) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory, source.code = code →
    (evaluateHOLFiniteState source program).2.clock = source.clock

theorem skip (code) : Preserves code .skip := by
  intro source installed
  rw [evaluateHOLFiniteState_skip]

theorem assign (code) (name : MlS) (expression : ExpHOL 64) : Preserves code (.assign .local name expression) := by
  intro source installed
  rw [evaluateHOLFiniteState_assign]
  split
  · rfl
  · split <;> rfl

theorem returned (code) (expression : ExpHOL 64) : Preserves code (.return expression) := by
  intro source installed
  rw [evaluateHOLFiniteState_return]
  split
  · rfl
  · split <;> rfl

theorem raised (code) (name : MlS) (expression : ExpHOL 64) : Preserves code (.raise name expression) := by
  intro source installed
  rw [evaluateHOLFiniteState_raise]
  simp only
  repeat first | rfl | split

theorem stopped (code) : Preserves code .break ∧ Preserves code .continue := by
  constructor <;> intro source installed
  · rw [evaluateHOLFiniteState_break]
  · rw [evaluateHOLFiniteState_continue]

theorem sequence (code) (first second : ProgHOL 64) (front : Preserves code first) (back : Preserves code second) :
    Preserves code (.seq first second) := by
  intro source installed
  have firstFrame := front source installed
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first = output at firstFrame ⊢
  obtain ⟨result, middle⟩ := output
  cases result with
  | none =>
    have codeEq := (Input.evaluation_fields source middle first none computed).2.2.2
    exact (back middle (codeEq.trans installed)).trans firstFrame
  | some result => exact firstFrame

theorem conditional (code) (test : ExpHOL 64) (yes no : ProgHOL 64) (left : Preserves code yes) (right : Preserves code no) :
    Preserves code (.ite test yes no) := by
  intro source installed
  rw [evaluateHOLFiniteState_ite]
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun address => Classical.propDecidable (source.memaddrs address)) test = value
  cases value with
  | none => rfl
  | some value =>
    cases value with
    | rStruct fields => rfl
    | nStruct name fields => rfl
    | val word =>
      cases word with
      | word word =>
        change (if word = 0 then evaluateHOLFiniteState source no else evaluateHOLFiniteState source yes).2.clock = source.clock
        by_cases zero : word = 0
        · rw [if_pos zero]; exact right source installed
        · rw [if_neg zero]; exact left source installed

theorem declared (code) (name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) (body : ProgHOL 64)
    (pureBody : Preserves code body) : Preserves code (.dec name shape expression body) := by
  intro source installed
  rw [evaluateHOLFiniteState_dec_total]
  simp only
  split
  · rfl
  · rename_i value read
    split
    · have frame := pureBody (setVarHOLFinite name value source) installed
      exact frame
    · rfl

theorem primitive (code) (name : MlS) (operator : PrimOp) (arguments : List (ExpHOL 64)) :
    Preserves code (.primitive name operator arguments) := by
  intro source installed
  rw [evaluateHOLFiniteState_primitive]
  repeat first | rfl | split

/-- Even failed ordinary stores spend no source call/loop clock. -/
theorem store (code) (address value : ExpHOL 64) : Preserves code (.store address value) := by
  intro source installed
  rw [evaluateHOLFiniteState_store]
  repeat first | rfl | split

end InitECandidate.Solver.Input.QuietClock

#print axioms InitECandidate.Solver.Input.QuietClock.skip
#print axioms InitECandidate.Solver.Input.QuietClock.assign
#print axioms InitECandidate.Solver.Input.QuietClock.returned
#print axioms InitECandidate.Solver.Input.QuietClock.raised
#print axioms InitECandidate.Solver.Input.QuietClock.stopped
#print axioms InitECandidate.Solver.Input.QuietClock.sequence
#print axioms InitECandidate.Solver.Input.QuietClock.conditional
#print axioms InitECandidate.Solver.Input.QuietClock.declared
#print axioms InitECandidate.Solver.Input.QuietClock.primitive
#print axioms InitECandidate.Solver.Input.QuietClock.store
