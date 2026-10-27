import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Input.NormalHostEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Outcomes which can resume a lexical context or return to a caller.
Exceptions and terminal failures have no host-frame assertion here. -/
def Resumes : Option (PanSemResultExact 64) → Prop
  | none => True
  | some (.returned _) => True
  | some .break => True
  | some .continue => True
  | _ => False

def host (source : PanSemStateFiniteExact 64 Guest.HostMemory) := source.ffi.ffiState

def Preserves (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (program : ProgHOL 64) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory, source.code = code →
    Resumes (evaluateHOLFiniteState source program).1 →
    host (evaluateHOLFiniteState source program).2 = host source

/-- A call only resumes after its actual body returned a checked value. -/
def Returning (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (program : ProgHOL 64) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory, source.code = code →
    ∀ value, (evaluateHOLFiniteState source program).1 = some (.returned value) →
      host (evaluateHOLFiniteState source program).2 = host source

theorem Preserves.returning {code} {program : ProgHOL 64} (pure : Preserves code program) : Returning code program := by
  intro source installed value actual
  exact pure source installed (by rw [actual]; trivial)

theorem skip (code) : Preserves code .skip := by
  intro source installed resumes
  rw [evaluateHOLFiniteState_skip]

theorem assign (code) (kind : VarKind) (name : MlS) (expression : ExpHOL 64) :
    Preserves code (.assign kind name expression) := by
  intro source installed resumes
  rw [evaluateHOLFiniteState_assign]
  cases kind <;> repeat first | rfl | split

theorem store (code) (address value : ExpHOL 64) : Preserves code (.store address value) := by
  intro source installed resumes
  rw [evaluateHOLFiniteState_store]
  repeat first | rfl | split

theorem byte_store (code) (address value : ExpHOL 64) : Preserves code (.storeByte address value) := by
  intro source installed resumes
  rw [evaluateHOLFiniteState_storeByte]
  repeat first | rfl | split

theorem returned (code) (expression : ExpHOL 64) : Preserves code (.return expression) := by
  intro source installed resumes
  rw [evaluateHOLFiniteState_return]
  repeat first | rfl | split

theorem raised (code) (identifier : MlS) (expression : ExpHOL 64) : Preserves code (.raise identifier expression) := by
  intro source installed resumes
  rw [evaluateHOLFiniteState_raise]
  simp only
  repeat first | rfl | split

theorem stopped (code) : Preserves code .break ∧ Preserves code .continue := by
  constructor <;> intro source installed resumes
  · rw [evaluateHOLFiniteState_break]
  · rw [evaluateHOLFiniteState_continue]

theorem sequence (code) (first second : ProgHOL 64)
    (front : Preserves code first) (back : Preserves code second) : Preserves code (.seq first second) := by
  intro source installed resumes
  rw [evaluateHOLFiniteState_seq_line780] at resumes ⊢
  generalize computed : evaluateHOLFiniteState source first = output at resumes ⊢
  obtain ⟨result, middle⟩ := output
  have frontFrame := front source installed
  rw [computed] at frontFrame
  cases result with
  | none =>
    have fields := evaluation_fields source middle first none computed
    exact (back middle (fields.2.2.2.trans installed) resumes).trans (frontFrame trivial)
  | some result => exact frontFrame resumes

theorem conditional (code) (test : ExpHOL 64) (yes no : ProgHOL 64)
    (left : Preserves code yes) (right : Preserves code no) : Preserves code (.ite test yes no) := by
  intro source installed resumes
  rw [evaluateHOLFiniteState_ite] at resumes ⊢
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun address => Classical.propDecidable (source.memaddrs address)) test = value at resumes ⊢
  cases value with
  | none => rfl
  | some value =>
    cases value with
    | rStruct fields => rfl
    | nStruct name fields => rfl
    | val payload =>
      cases payload with
      | word word =>
        simp only at resumes
        change host (if word = 0 then evaluateHOLFiniteState source no else evaluateHOLFiniteState source yes).2 = host source
        by_cases zero : word = 0
        · rw [if_pos zero] at resumes ⊢; exact right source installed resumes
        · rw [if_neg zero] at resumes ⊢; exact left source installed resumes

theorem declared (code) (name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) (body : ProgHOL 64)
    (pureBody : Preserves code body) : Preserves code (.dec name shape expression body) := by
  intro source installed resumes
  rw [evaluateHOLFiniteState_dec_total] at resumes ⊢
  cases read : @evalHOLExact 64 Guest.HostMemory _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) expression with
  | none => simp only [read]
  | some value =>
    simp only [read] at resumes ⊢
    by_cases checked : shapeEqHOL shape (shapeOfHOLExact value) = true
    · rw [if_pos checked] at resumes ⊢
      exact pureBody (setVarHOLFinite name value source) installed resumes
    · rw [if_neg checked]

theorem primitive (code) (name : MlS) (operator : PrimOp) (arguments : List (ExpHOL 64)) :
    Preserves code (.primitive name operator arguments) := by
  intro source installed resumes
  rw [evaluateHOLFiniteState_primitive]
  repeat first | rfl | split

end InitECandidate.Solver.Input.NormalHostEffects

#print axioms InitECandidate.Solver.Input.NormalHostEffects.Preserves.returning
#print axioms InitECandidate.Solver.Input.NormalHostEffects.skip
#print axioms InitECandidate.Solver.Input.NormalHostEffects.assign
#print axioms InitECandidate.Solver.Input.NormalHostEffects.store
#print axioms InitECandidate.Solver.Input.NormalHostEffects.byte_store
#print axioms InitECandidate.Solver.Input.NormalHostEffects.returned
#print axioms InitECandidate.Solver.Input.NormalHostEffects.raised
#print axioms InitECandidate.Solver.Input.NormalHostEffects.stopped
#print axioms InitECandidate.Solver.Input.NormalHostEffects.sequence
#print axioms InitECandidate.Solver.Input.NormalHostEffects.conditional
#print axioms InitECandidate.Solver.Input.NormalHostEffects.declared
#print axioms InitECandidate.Solver.Input.NormalHostEffects.primitive
