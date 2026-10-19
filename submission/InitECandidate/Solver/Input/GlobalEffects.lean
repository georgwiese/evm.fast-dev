import InitECandidate.Solver.Input.LocalEffects
import InitECandidate.Solver.Input.ReturnNormal
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Input.GlobalEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- Observe one selected global and the immutable code. Memory, FFI,
local bindings and clock may change independently. -/
def erase (key : MlS) (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  (source.code,source.globals.lookup key)

def Preserves (key : MlS) (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (program : ProgHOL 64) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,source.code=code →
    erase key (evaluateHOLFiniteState source program).2=erase key source

theorem code_of_erase (key : MlS) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (same : erase key target=erase key source) : target.code=source.code := congrArg Prod.fst same

theorem skip (key : MlS) (code) : Preserves key code .skip := by
  intro source installed
  rw [evaluateHOLFiniteState_skip]

theorem assign (key : MlS) (code) (name : MlS) (expression : ExpHOL 64) : Preserves key code (.assign .local name expression) := by
  intro source installed
  rw [evaluateHOLFiniteState_assign]
  split
  · rfl
  · split <;> rfl

theorem returned (key : MlS) (code) (expression : ExpHOL 64) : Preserves key code (.return expression) := by
  intro source installed
  rw [evaluateHOLFiniteState_return]
  split
  · rfl
  · split <;> rfl

theorem raised (key : MlS) (code) (name : MlS) (expression : ExpHOL 64) : Preserves key code (.raise name expression) := by
  intro source installed
  rw [evaluateHOLFiniteState_raise]
  simp only
  repeat first | rfl | split

theorem stopped (key : MlS) (code) : Preserves key code .break ∧ Preserves key code .continue := by
  constructor <;> intro source installed
  · rw [evaluateHOLFiniteState_break]
  · rw [evaluateHOLFiniteState_continue]

theorem sequence (key : MlS) (code) (first second : ProgHOL 64) (front : Preserves key code first) (back : Preserves key code second) :
    Preserves key code (.seq first second) := by
  intro source installed
  have firstFrame := front source installed
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first = output at firstFrame ⊢
  obtain ⟨result, middle⟩ := output
  cases result with
  | none =>
    have codeEq := code_of_erase key source middle firstFrame
    exact (back middle (codeEq.trans installed)).trans firstFrame
  | some result => exact firstFrame

theorem conditional (key : MlS) (code) (test : ExpHOL 64) (yes no : ProgHOL 64) (left : Preserves key code yes) (right : Preserves key code no) :
    Preserves key code (.ite test yes no) := by
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
        change erase key (if word = 0 then evaluateHOLFiniteState source no else evaluateHOLFiniteState source yes).2 = erase key source
        by_cases zero : word = 0
        · rw [if_pos zero]; exact right source installed
        · rw [if_neg zero]; exact left source installed

theorem declared (key : MlS) (code) (name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) (body : ProgHOL 64)
    (pureBody : Preserves key code body) : Preserves key code (.dec name shape expression body) := by
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

end InitECandidate.Solver.Input.GlobalEffects

#print axioms InitECandidate.Solver.Input.GlobalEffects.skip
#print axioms InitECandidate.Solver.Input.GlobalEffects.assign
#print axioms InitECandidate.Solver.Input.GlobalEffects.returned
#print axioms InitECandidate.Solver.Input.GlobalEffects.raised
#print axioms InitECandidate.Solver.Input.GlobalEffects.stopped
#print axioms InitECandidate.Solver.Input.GlobalEffects.sequence
#print axioms InitECandidate.Solver.Input.GlobalEffects.conditional
#print axioms InitECandidate.Solver.Input.GlobalEffects.declared

#print axioms InitECandidate.Solver.Input.GlobalEffects.code_of_erase
