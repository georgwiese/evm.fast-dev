import InitECandidate.Solver.Input.MemoryMetadata
import InitECandidate.Solver.Input.LocalEffectsScoped

namespace InitECandidate.Solver.Input.MemoryEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Effects that may write memory and locals but retain all other runtime
fields, including every global and FFI state. This is no runtime bound. -/
abbrev erase := MemoryMetadata.erase

def Preserves (code : HolFiniteMapExact MlS (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (program : ProgHOL 64) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,source.code=code→erase (evaluateHOLFiniteState source program).2=erase source

theorem code_of_erase (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : erase target=erase source) :
    target.code=source.code := MemoryMetadata.code frame

theorem of_readonly (code) (program : ProgHOL 64) (pure : LocalEffects.Preserves code program) : Preserves code program := by
  intro source installed
  exact MemoryMetadata.of_frame (pure source installed)

theorem skip (code) : Preserves code .skip := of_readonly code .skip (LocalEffects.skip code)
theorem assign (code) (name : MlS) (expression : ExpHOL 64) : Preserves code (.assign .local name expression) :=
  of_readonly code _ (LocalEffects.assign code name expression)
theorem returned (code) (expression : ExpHOL 64) : Preserves code (.return expression) :=
  of_readonly code _ (LocalEffects.returned code expression)
theorem raised (code) (name : MlS) (expression : ExpHOL 64) : Preserves code (.raise name expression) :=
  of_readonly code _ (LocalEffects.raised code name expression)

theorem store (code) (address value : ExpHOL 64) : Preserves code (.store address value) := by
  intro source installed
  rw [evaluateHOLFiniteState_store]
  repeat first | rfl | split

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


theorem loop (code) (test : ExpHOL 64) (body : ProgHOL 64) (pureBody : Preserves code body) :
    Preserves code (.while test body) := by
  classical
  have auxiliary : ∀ clock (source : PanSemStateFiniteExact 64 Guest.HostMemory), source.clock = clock → source.code = code →
      erase (evaluateHOLFiniteState source (.while test body)).2 = erase source := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro source clockEq installed
      rw [evaluateHOLFiniteState_while_total]
      generalize observed : @evalHOLFinite 64 Guest.HostMemory _ source
        (fun address => Classical.propDecidable (source.memaddrs address)) test = value
      cases value with
      | none => rfl
      | some value =>
        cases value with
        | rStruct fields => rfl
        | nStruct name fields => rfl
        | val payload =>
          cases payload with
          | word word =>
            simp only
            by_cases nonzero : word ≠ 0
            · rw [if_pos nonzero]
              by_cases zero : source.clock = 0
              · rw [if_pos zero]
                rfl
              · rw [if_neg zero]
                have bodyFrame := pureBody (decClockHOLFinite source) installed
                have bodyClock := evaluateHOLFiniteState_clock_le (decClockHOLFinite source) body
                generalize computed : evaluateHOLFiniteState (decClockHOLFinite source) body = output at bodyFrame bodyClock ⊢
                obtain ⟨result, target⟩ := output
                have fixed := WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite source) target result bodyClock
                simp only [fixed]
                have targetCode : target.code = code := (code_of_erase (decClockHOLFinite source) target bodyFrame).trans installed
                have earlier : target.clock < clock := by change target.clock ≤ source.clock - 1 at bodyClock; omega
                have tailFrame := ih target.clock earlier target rfl targetCode
                cases result with
                | none => exact tailFrame.trans bodyFrame
                | some result =>
                  cases result <;> first | exact tailFrame.trans bodyFrame | exact bodyFrame
            · rw [if_neg nonzero]
  intro source installed
  exact auxiliary source.clock source rfl installed


theorem scoped_call (code) (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (calleePure : ∀ values body callee returnShape, lookupCodeHOLFinite code.lookup function values = some (body, callee, returnShape) → Preserves code body)
    (pureContinuation : Preserves code continuation) : Preserves code (.decCall name shape function arguments continuation) := by
  classical
  intro source installed
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args]
  | some values =>
    simp only [args]
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called]
    | some data =>
      obtain ⟨body, callee, returnShape⟩ := data
      simp only [called]
      by_cases zero : source.clock = 0
      · rw [if_pos zero]; rfl
      · rw [if_neg zero]
        have lookup : lookupCodeHOLFinite code.lookup function values = some (body, callee, returnShape) := by rw [← installed]; exact called
        have frame := calleePure values body callee returnShape lookup (callEntryStateHOLFinite source callee) installed
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at frame ⊢
        obtain ⟨result, target⟩ := output
        have postFrame : erase target = erase source := frame
        cases result with
        | none => exact postFrame
        | some result =>
          cases result with
          | returned returned =>
            simp only
            split
            · have codeEq : target.code = code := (code_of_erase source target postFrame).trans installed
              have tailFrame := pureContinuation (setVarHOLFinite name returned {target with locals := source.locals}) codeEq
              exact tailFrame.trans postFrame
            · exact postFrame
          | error => exact postFrame
          | timeOut => exact postFrame
          | «break» => exact postFrame
          | «continue» => exact postFrame
          | exception identifier payload => exact postFrame
          | finalFfi event => exact postFrame

theorem scoped_body (code) (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (entry : code.lookup function = some (formals, body, returnShape))
    (pureBody : Preserves code body) (pureContinuation : Preserves code continuation) :
    Preserves code (.decCall name shape function arguments continuation) := by
  apply scoped_call
  · intro values actual callee actualShape lookedUp
    rw [LocalEffects.lookup_body code function formals body returnShape entry values actual callee actualShape lookedUp]
    exact pureBody
  · exact pureContinuation


end InitECandidate.Solver.Input.MemoryEffects

#print axioms InitECandidate.Solver.Input.MemoryEffects.of_readonly

#print axioms InitECandidate.Solver.Input.MemoryEffects.store

#print axioms InitECandidate.Solver.Input.MemoryEffects.sequence

#print axioms InitECandidate.Solver.Input.MemoryEffects.conditional

#print axioms InitECandidate.Solver.Input.MemoryEffects.declared

#print axioms InitECandidate.Solver.Input.MemoryEffects.loop

#print axioms InitECandidate.Solver.Input.MemoryEffects.scoped_body
