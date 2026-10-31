import InitECandidate.Solver.Input.LocalEffects
import InitECandidate.Solver.Input.LocalEffectsCall

namespace InitECandidate.Solver.Input.MemoryMetadata
open Flapjack PanSemStateFiniteExact

/-- All physical fields except memory, locals and clock. -/
def erase (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  emptyLocalsHOLFinite {source with memory := fun _ => .word 0#64,clock := 0}

theorem domain {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (frame : erase target = erase source) :
    target.memaddrs = source.memaddrs := by
  have projected := congrArg PanSemStateFiniteExact.memaddrs frame
  exact projected

theorem endian {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (frame : erase target = erase source) :
    target.be = source.be := by
  have projected := congrArg PanSemStateFiniteExact.be frame
  exact projected

theorem code {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (frame : erase target = erase source) :
    target.code = source.code := by
  have projected := congrArg PanSemStateFiniteExact.code frame
  exact projected

theorem of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (frame : LocalEffects.erase target = LocalEffects.erase source) :
    erase target = erase source := by
  have projected := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with memory := fun _ => .word 0#64}) frame
  exact projected

end InitECandidate.Solver.Input.MemoryMetadata

#print axioms InitECandidate.Solver.Input.MemoryMetadata.domain
#print axioms InitECandidate.Solver.Input.MemoryMetadata.endian

namespace InitECandidate.Solver.Input.MemoryMetadata
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- All outcomes retain every field except memory, locals and clock.
This property permits actual stores, without asserting their success. -/
def Preserves (code : HolFiniteMapExact MlS (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (program : ProgHOL 64) : Prop:=
  ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,source.code=code→erase (evaluateHOLFiniteState source program).2=erase source

theorem skip (code) : Preserves code .skip:=by intro source installed; rw [evaluateHOLFiniteState_skip]

theorem assign (code) (name : MlS) (expression : ExpHOL 64) : Preserves code (.assign .local name expression) := by
  intro source installed
  rw [evaluateHOLFiniteState_assign]
  repeat first | rfl | split

theorem store (code) (address value : ExpHOL 64) : Preserves code (.store address value) := by
  intro source installed
  rw [evaluateHOLFiniteState_store]
  repeat first | rfl | split

theorem byte_store (code) (address value : ExpHOL 64) : Preserves code (.storeByte address value) := by
  intro source installed
  rw [evaluateHOLFiniteState_storeByte]
  repeat first | rfl | split

theorem returned (code) (expression : ExpHOL 64) : Preserves code (.return expression) := by
  intro source installed
  rw [evaluateHOLFiniteState_return]
  repeat first | rfl | split

theorem sequence (code) (first second : ProgHOL 64) (front : Preserves code first) (back : Preserves code second) :
    Preserves code (.seq first second) := by
  intro source installed
  have firstFrame:=front source installed
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first=output at firstFrame ⊢
  obtain ⟨result,middle⟩:=output
  cases result with
  | none=>exact (back middle ((MemoryMetadata.code firstFrame).trans installed)).trans firstFrame
  | some result=>exact firstFrame

theorem conditional (code) (test : ExpHOL 64) (yes no : ProgHOL 64) (left : Preserves code yes) (right : Preserves code no) :
    Preserves code (.ite test yes no) := by
  intro source installed
  rw [evaluateHOLFiniteState_ite]
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact (fun address=>Classical.propDecidable (source.memaddrs address)) test=value
  cases value with
  | none=>rfl
  | some value=>
    cases value with
    | rStruct fields=>rfl
    | nStruct name fields=>rfl
    | val payload=>
      cases payload with
      | word word=>
        change erase (if word=0 then evaluateHOLFiniteState source no else evaluateHOLFiniteState source yes).2=erase source
        by_cases zero : word=0
        · rw [if_pos zero]; exact right source installed
        · rw [if_neg zero]; exact left source installed

theorem declared (code) (name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) (body : ProgHOL 64) (pureBody : Preserves code body) :
    Preserves code (.dec name shape expression body) := by
  intro source installed
  rw [evaluateHOLFiniteState_dec_total]
  simp only
  split
  · rfl
  · rename_i value read
    split
    · exact pureBody (setVarHOLFinite name value source) installed
    · rfl

theorem loop (code) (test : ExpHOL 64) (body : ProgHOL 64) (pureBody : Preserves code body) : Preserves code (.while test body) := by
  classical
  have auxiliary : ∀ clock (source : PanSemStateFiniteExact 64 Guest.HostMemory),source.clock=clock→source.code=code→
      erase (evaluateHOLFiniteState source (.while test body)).2=erase source:=by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih=>
      intro source clockEq installed
      rw [evaluateHOLFiniteState_while_total]
      generalize observed : @evalHOLFinite 64 Guest.HostMemory _ source (fun address=>Classical.propDecidable (source.memaddrs address)) test=value
      cases value with
      | none=>rfl
      | some value=>
        cases value with
        | rStruct fields=>rfl
        | nStruct name fields=>rfl
        | val payload=>
          cases payload with
          | word word=>
            simp only
            by_cases nonzero : word≠0
            · rw [if_pos nonzero]
              by_cases zero : source.clock=0
              · rw [if_pos zero]; rfl
              · rw [if_neg zero]
                have bodyFrame:=pureBody (decClockHOLFinite source) installed
                have bodyClock:=evaluateHOLFiniteState_clock_le (decClockHOLFinite source) body
                generalize computed : evaluateHOLFiniteState (decClockHOLFinite source) body=output at bodyFrame bodyClock ⊢
                obtain ⟨result,target⟩:=output
                have fixed:=WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite source) target result bodyClock
                simp only [fixed]
                have targetCode : target.code=code:=(MemoryMetadata.code bodyFrame).trans installed
                have earlier : target.clock<clock:=by change target.clock≤source.clock-1 at bodyClock; omega
                have tailFrame:=ih target.clock earlier target rfl targetCode
                cases result with
                | none=>exact tailFrame.trans bodyFrame
                | some result=>cases result <;> first | exact tailFrame.trans bodyFrame | exact bodyFrame
            · rw [if_neg nonzero]
  intro source installed
  exact auxiliary source.clock source rfl installed

theorem called (code) (destination : Option (Option MlS)) (function : MlS) (arguments : List (ExpHOL 64))
    (calleePure : ∀ values body callee shape,lookupCodeHOLFinite code.lookup function values=some (body,callee,shape)→Preserves code body) :
    Preserves code (.call (LocalEffects.callInfo destination) function arguments) := by
  classical
  intro source installed
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments with
  | none=>simp only [args]
  | some values=>
    simp only [args]
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none=>simp only [called]
    | some data=>
      obtain ⟨body,callee,shape⟩:=data
      simp only [called]
      by_cases zero : source.clock=0
      · rw [if_pos zero]; rfl
      · rw [if_neg zero]
        have lookup : lookupCodeHOLFinite code.lookup function values=some (body,callee,shape):=by rw [←installed]; exact called
        have frame:=calleePure values body callee shape lookup (callEntryStateHOLFinite source callee) installed
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output at frame ⊢
        obtain ⟨result,target⟩:=output
        have postFrame : erase target=erase source:=frame
        cases destination with
        | none=>
          cases result with
          | none=>exact postFrame
          | some result=>
            cases result <;> simp only [LocalEffects.callInfo,Option.map_none]
            all_goals repeat first | exact postFrame | split
        | some destination=>
          cases destination with
          | none=>
            cases result with
            | none=>exact postFrame
            | some result=>
              cases result <;> simp only [LocalEffects.callInfo,Option.map_some,Option.map_none]
              all_goals repeat first | exact postFrame | split
          | some name=>
            cases result with
            | none=>exact postFrame
            | some result=>
              cases result <;> simp only [LocalEffects.callInfo,Option.map_some]
              all_goals repeat first | exact postFrame | split

theorem call_body (code) (destination : Option (Option MlS)) (function : MlS) (arguments : List (ExpHOL 64))
    (formals : List (MlS×ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL)
    (entry : code.lookup function=some (formals,body,shape)) (pureBody : Preserves code body) :
    Preserves code (.call (LocalEffects.callInfo destination) function arguments) := by
  apply called
  intro values actual callee returnShape lookedUp
  rw [LocalEffects.lookup_body code function formals body shape entry values actual callee returnShape lookedUp]
  exact pureBody

end InitECandidate.Solver.Input.MemoryMetadata

#print axioms InitECandidate.Solver.Input.MemoryMetadata.assign
#print axioms InitECandidate.Solver.Input.MemoryMetadata.store
#print axioms InitECandidate.Solver.Input.MemoryMetadata.byte_store
#print axioms InitECandidate.Solver.Input.MemoryMetadata.returned
#print axioms InitECandidate.Solver.Input.MemoryMetadata.sequence
#print axioms InitECandidate.Solver.Input.MemoryMetadata.conditional
#print axioms InitECandidate.Solver.Input.MemoryMetadata.declared
#print axioms InitECandidate.Solver.Input.MemoryMetadata.loop
#print axioms InitECandidate.Solver.Input.MemoryMetadata.call_body
