import InitECandidate.Solver.Input.NormalHostEffects
import InitECandidate.Solver.Input.GlobalByteEffects

namespace InitECandidate.Solver.Input.NormalHeapEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A current scalar allocator cursor above a retained lower frontier. -/
def AtLeast (lower : Nat) (state : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop :=
  ∃ pointer : BitVec 64, state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) ∧
    lower ≤ pointer.toNat ∧ pointer.toNat ≤ 2952790016 ∧ pointer.toNat % 8 = 0

/-- Resuming statements retain every valid incoming heap frontier. This is
an ownership invariant, not an iteration count or runtime bound. -/
def Preserves (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (program : ProgHOL 64) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory, source.code = code →
    ∀ lower, AtLeast lower source → NormalHostEffects.Resumes (evaluateHOLFiniteState source program).1 →
      AtLeast lower (evaluateHOLFiniteState source program).2

def Returning (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (program : ProgHOL 64) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory, source.code = code →
    ∀ lower, AtLeast lower source → ∀ value,
      (evaluateHOLFiniteState source program).1 = some (.returned value) →
      AtLeast lower (evaluateHOLFiniteState source program).2

theorem Preserves.returning {code} {program : ProgHOL 64} (pure : Preserves code program) : Returning code program := by
  intro source installed lower initial value actual
  exact pure source installed lower initial (by rw [actual]; trivial)

theorem of_global (code) (program : ProgHOL 64)
    (pure : GlobalEffects.Preserves (ofString "heap_ptr") code program) : Preserves code program := by
  intro source installed lower initial resumes
  obtain ⟨pointer, cell, lowerBound, upperBound, aligned⟩ := initial
  have same := congrArg Prod.snd (pure source installed)
  exact ⟨pointer, same.trans cell, lowerBound, upperBound, aligned⟩

theorem skip (code) : Preserves code .skip := of_global code .skip (GlobalEffects.skip _ code)

theorem assign (code) (name : MlS) (expression : ExpHOL 64) : Preserves code (.assign .local name expression) :=
  of_global code _ (GlobalEffects.assign _ code name expression)

theorem global_other (code) (name : MlS) (expression : ExpHOL 64) (other : ofString "heap_ptr" ≠ name) :
    Preserves code (.assign .global name expression) := of_global code _ (GlobalEffects.global_other _ code name expression other)

theorem store (code) (address value : ExpHOL 64) : Preserves code (.store address value) :=
  of_global code _ (GlobalEffects.store _ code address value)

theorem byte_store (code) (address value : ExpHOL 64) : Preserves code (.storeByte address value) :=
  of_global code _ (GlobalEffects.byte_store _ code address value)

theorem returned (code) (expression : ExpHOL 64) : Preserves code (.return expression) :=
  of_global code _ (GlobalEffects.returned _ code expression)

theorem raised (code) (identifier : MlS) (expression : ExpHOL 64) : Preserves code (.raise identifier expression) :=
  of_global code _ (GlobalEffects.raised _ code identifier expression)

theorem stopped (code) : Preserves code .break ∧ Preserves code .continue :=
  ⟨of_global code _ (GlobalEffects.stopped _ code).1, of_global code _ (GlobalEffects.stopped _ code).2⟩

theorem shared_load (code) (operator : OpSize) (name : MlS) (expression : ExpHOL 64) :
    Preserves code (.shMemLoad operator .local name expression) :=
  of_global code _ (GlobalEffects.shared_load _ code operator name expression)

theorem sequence (code) (first second : ProgHOL 64)
    (front : Preserves code first) (back : Preserves code second) : Preserves code (.seq first second) := by
  intro source installed lower initial resumes
  rw [evaluateHOLFiniteState_seq_line780] at resumes ⊢
  generalize computed : evaluateHOLFiniteState source first = output at resumes ⊢
  obtain ⟨result, middle⟩ := output
  have frontFrame := front source installed lower initial
  rw [computed] at frontFrame
  cases result with
  | none =>
    have codeEq := (evaluation_fields source middle first none computed).2.2.2.trans installed
    exact back middle codeEq lower (frontFrame trivial) resumes
  | some result => exact frontFrame resumes

theorem conditional (code) (test : ExpHOL 64) (yes no : ProgHOL 64)
    (left : Preserves code yes) (right : Preserves code no) : Preserves code (.ite test yes no) := by
  intro source installed lower initial resumes
  rw [evaluateHOLFiniteState_ite] at resumes ⊢
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun address => Classical.propDecidable (source.memaddrs address)) test = value at resumes ⊢
  cases value with
  | none => exact initial
  | some value =>
    cases value with
    | rStruct fields => exact initial
    | nStruct name fields => exact initial
    | val payload =>
      cases payload with
      | word word =>
        simp only at resumes ⊢
        by_cases zero : word = 0
        · rw [if_pos zero] at resumes ⊢; exact right source installed lower initial resumes
        · rw [if_neg zero] at resumes ⊢; exact left source installed lower initial resumes

theorem declared (code) (name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) (body : ProgHOL 64)
    (pureBody : Preserves code body) : Preserves code (.dec name shape expression body) := by
  intro source installed lower initial resumes
  rw [evaluateHOLFiniteState_dec_total] at resumes ⊢
  cases read : @evalHOLExact 64 Guest.HostMemory _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) expression with
  | none => simp only [read]; exact initial
  | some value =>
    simp only [read] at resumes ⊢
    by_cases checked : shapeEqHOL shape (shapeOfHOLExact value) = true
    · rw [if_pos checked] at resumes ⊢
      exact pureBody (setVarHOLFinite name value source) installed lower initial resumes
    · rw [if_neg checked]; exact initial

end InitECandidate.Solver.Input.NormalHeapEffects

#print axioms InitECandidate.Solver.Input.NormalHeapEffects.Preserves.returning
#print axioms InitECandidate.Solver.Input.NormalHeapEffects.of_global
#print axioms InitECandidate.Solver.Input.NormalHeapEffects.skip
#print axioms InitECandidate.Solver.Input.NormalHeapEffects.assign
#print axioms InitECandidate.Solver.Input.NormalHeapEffects.global_other
#print axioms InitECandidate.Solver.Input.NormalHeapEffects.store
#print axioms InitECandidate.Solver.Input.NormalHeapEffects.byte_store
#print axioms InitECandidate.Solver.Input.NormalHeapEffects.returned
#print axioms InitECandidate.Solver.Input.NormalHeapEffects.raised
#print axioms InitECandidate.Solver.Input.NormalHeapEffects.stopped
#print axioms InitECandidate.Solver.Input.NormalHeapEffects.shared_load
#print axioms InitECandidate.Solver.Input.NormalHeapEffects.sequence
#print axioms InitECandidate.Solver.Input.NormalHeapEffects.conditional
#print axioms InitECandidate.Solver.Input.NormalHeapEffects.declared
