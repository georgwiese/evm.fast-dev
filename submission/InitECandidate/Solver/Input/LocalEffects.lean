import InitECandidate.Solver.Input.EvaluationFields
import InitECandidate.Solver.Input.ReturnNormal
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Input.LocalEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- Erase only local bindings and clock. Equality retains memory, globals,
FFI, domain and every other source field, including on exceptional outcomes. -/
def erase (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  emptyLocalsHOLFinite {source with clock := 0}

def Preserves (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (program : ProgHOL 64) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory, source.code = code →
    erase (evaluateHOLFiniteState source program).2 = erase source

theorem code_of_erase (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (same : erase target = erase source) :
    target.code = source.code := by
  have projected := congrArg PanSemStateFiniteExact.code same
  exact projected

theorem memory_of_erase (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (same : erase target = erase source) :
    target.memory = source.memory := by
  have projected := congrArg PanSemStateFiniteExact.memory same
  exact projected

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
    have codeEq := code_of_erase source middle firstFrame
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
        change erase (if word = 0 then evaluateHOLFiniteState source no else evaluateHOLFiniteState source yes).2 = erase source
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

end InitECandidate.Solver.Input.LocalEffects

#print axioms InitECandidate.Solver.Input.LocalEffects.skip
#print axioms InitECandidate.Solver.Input.LocalEffects.assign
#print axioms InitECandidate.Solver.Input.LocalEffects.returned
#print axioms InitECandidate.Solver.Input.LocalEffects.raised
#print axioms InitECandidate.Solver.Input.LocalEffects.stopped
#print axioms InitECandidate.Solver.Input.LocalEffects.sequence
#print axioms InitECandidate.Solver.Input.LocalEffects.conditional
#print axioms InitECandidate.Solver.Input.LocalEffects.declared

#print axioms InitECandidate.Solver.Input.LocalEffects.code_of_erase
#print axioms InitECandidate.Solver.Input.LocalEffects.memory_of_erase
