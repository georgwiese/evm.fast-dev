import InitECandidate.Solver.Input.LocalEffects
import InitECandidate.Solver.Input.EvaluationOracle
import InitE.SourceSemantics

namespace InitECandidate.Solver.Input.ReadHostEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Observe host bytes only; real shared reads may append FFI events. -/
def host (source : PanSemStateFiniteExact 64 Guest.HostMemory) := source.ffi.ffiState

/-- All-outcome host equality for actual code under the fixed source oracle.
This interface is for read-only host accesses, not output stores or traps. -/
def Preserves (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (program : ProgHOL 64) : Prop :=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory, source.code = code →
    source.ffi.oracle = InitE.sourceOracle →
    host (evaluateHOLFiniteState source program).2 = host source

theorem of_local (code) (program : ProgHOL 64) (pure : LocalEffects.Preserves code program) : Preserves code program := by
  intro source installed oracle
  have framed := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.ffi.ffiState) (pure source installed)
  exact framed

theorem skip (code) : Preserves code .skip := of_local code .skip (LocalEffects.skip code)

theorem assign (code) (name : MlS) (expression : ExpHOL 64) : Preserves code (.assign .local name expression) :=
  of_local code _ (LocalEffects.assign code name expression)

theorem store (code) (address value : ExpHOL 64) : Preserves code (.store address value) := by
  intro source installed oracle
  rw [evaluateHOLFiniteState_store]
  repeat first | rfl | split

theorem byte_store (code) (address value : ExpHOL 64) : Preserves code (.storeByte address value) := by
  intro source installed oracle
  rw [evaluateHOLFiniteState_storeByte]
  repeat first | rfl | split

theorem returned (code) (expression : ExpHOL 64) : Preserves code (.return expression) :=
  of_local code _ (LocalEffects.returned code expression)

theorem raised (code) (identifier : MlS) (expression : ExpHOL 64) : Preserves code (.raise identifier expression) :=
  of_local code _ (LocalEffects.raised code identifier expression)

theorem stopped (code) : Preserves code .break ∧ Preserves code .continue :=
  ⟨of_local code _ (LocalEffects.stopped code).1, of_local code _ (LocalEffects.stopped code).2⟩

theorem oracle_return_host (source next : Guest.HostMemory) (configuration bytes answer : List (BitVec 8))
    (run : InitE.sourceOracle (.sharedMem .mappedRead) source configuration bytes = .ret next answer) :
    next = source := by
  cases read : (List.range (Guest.sharedWidth (configuration.map bitsToByte))).mapM
      (fun index => source (Guest.wordOfLeBytes (bytes.map bitsToByte) + BitVec.ofNat 64 index)) with
  | none => simp only [InitE.sourceOracle, Guest.guestOracle, read] at run; cases run
  | some values =>
    simp only [InitE.sourceOracle, Guest.guestOracle, read] at run
    exact (HolOracleResult.ret.inj run).1.symm

/-- The real source read wrapper cannot change the host on a returned reply,
including arbitrary access widths and the actual wrapper length check. -/
theorem ffi_return_host (source : HolFfiState Guest.HostMemory) (configuration bytes : List (BitVec 8))
    {next : HolFfiState Guest.HostMemory} {answer : List (BitVec 8)}
    (oracle : source.oracle = InitE.sourceOracle)
    (run : callFFIHOL source (.sharedMem .mappedRead) configuration bytes = .ret next answer) :
    next.ffiState = source.ffiState := by
  cases reply : source.oracle (.sharedMem .mappedRead) source.ffiState configuration bytes with
  | final outcome => simp [callFFIHOL, reply] at run
  | ret memory values =>
    have canonical := reply
    rw [oracle] at canonical
    have memoryEq := oracle_return_host source.ffiState memory configuration bytes values canonical
    by_cases fits : values.length = bytes.length
    · simp only [callFFIHOL, reduceCtorEq, ↓reduceIte, reply, fits] at run
      exact (congrArg HolFfiState.ffiState (HolFfiResult.ret.inj run).1).symm.trans memoryEq
    · simp [callFFIHOL, reply, fits] at run

/-- A shared read retains host bytes even when its address/read/shape fails,
its byte backing is absent, or its oracle reply is terminal. -/
theorem shared_load (code) (operator : OpSize) (name : MlS) (expression : ExpHOL 64) :
    Preserves code (.shMemLoad operator .local name expression) := by
  classical
  intro source installed oracle
  rw [evaluateHOLFiniteState_shMemLoad_source]
  simp only [shMemLoadHOLFiniteExact]
  repeat' first
    | rfl
    | unfold setKvarFfiHOLFinite
    | unfold setKvarHOLFinite
    | unfold setVarHOLFinite
    | split
    | exact ffi_return_host source.ffi _ _ oracle (by assumption)

theorem sequence (code) (first second : ProgHOL 64)
    (front : Preserves code first) (back : Preserves code second) : Preserves code (.seq first second) := by
  intro source installed oracle
  have frame := front source installed oracle
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first = output at frame ⊢
  obtain ⟨result, middle⟩ := output
  cases result with
  | none =>
    have codeEq := (evaluation_fields source middle first none computed).2.2.2
    have oracleEq := evaluation_oracle source middle first none computed
    exact (back middle (codeEq.trans installed) (oracleEq.trans oracle)).trans frame
  | some result => exact frame

theorem conditional (code) (test : ExpHOL 64) (yes no : ProgHOL 64)
    (left : Preserves code yes) (right : Preserves code no) : Preserves code (.ite test yes no) := by
  intro source installed oracle
  rw [evaluateHOLFiniteState_ite]
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
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
        change host (if word = 0 then evaluateHOLFiniteState source no else evaluateHOLFiniteState source yes).2 = host source
        by_cases zero : word = 0
        · rw [if_pos zero]; exact right source installed oracle
        · rw [if_neg zero]; exact left source installed oracle

theorem declared (code) (name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) (body : ProgHOL 64)
    (pureBody : Preserves code body) : Preserves code (.dec name shape expression body) := by
  intro source installed oracle
  rw [evaluateHOLFiniteState_dec_total]
  simp only
  split
  · rfl
  · split
    · exact pureBody (setVarHOLFinite name _ source) installed oracle
    · rfl

end InitECandidate.Solver.Input.ReadHostEffects

#print axioms InitECandidate.Solver.Input.ReadHostEffects.of_local
#print axioms InitECandidate.Solver.Input.ReadHostEffects.skip
#print axioms InitECandidate.Solver.Input.ReadHostEffects.assign
#print axioms InitECandidate.Solver.Input.ReadHostEffects.store
#print axioms InitECandidate.Solver.Input.ReadHostEffects.byte_store
#print axioms InitECandidate.Solver.Input.ReadHostEffects.returned
#print axioms InitECandidate.Solver.Input.ReadHostEffects.raised
#print axioms InitECandidate.Solver.Input.ReadHostEffects.stopped
#print axioms InitECandidate.Solver.Input.ReadHostEffects.shared_load
#print axioms InitECandidate.Solver.Input.ReadHostEffects.sequence
#print axioms InitECandidate.Solver.Input.ReadHostEffects.conditional
#print axioms InitECandidate.Solver.Input.ReadHostEffects.declared

#print axioms InitECandidate.Solver.Input.ReadHostEffects.ffi_return_host

#print axioms InitECandidate.Solver.Input.ReadHostEffects.oracle_return_host
