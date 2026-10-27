import InitECandidate.Solver.Input.SourceEntry
import InitECandidate.Solver.Input.MainProgram
import InitECandidate.Solver.Input.OriginalArenaGlobals
import InitECandidate.Solver.Input.OriginalScalarGlobals
import InitECandidate.Solver.Input.TailCallTerminating
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem nullary_environment (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (name : MlS) (program : ProgHOL 64) (entry : code name = some ([],program,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite code name [] = some (program,callee,.one) := by
  have raw : lookupCodeHOLExact code name [] = some (program,(fun _ => none),.one) := by simp [lookupCodeHOLExact,entry]
  obtain ⟨callee,called,_⟩ := WitnessRadix.CodeEnvironment.finite_lookup code name [] program _ .one raw
  exact ⟨callee,called⟩

/-- Facts supplied by the authoritative declaration/entry semantics, before
any guest initialization call. The input list has no length premise. -/
structure Entry (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  code : OriginalCode.Installed source.code
  shapes : OriginalExceptions.Installed source.eshapes
  scalars : OriginalScalarGlobals.Scalars source.globals
  zeros : ∀ key,key ∈ OriginalScalarGlobals.names → source.globals.lookup key = some (.val (.word 0#64))
  base : source.baseAddr = BitVec.ofNat 64 InitE.sourceBase
  memory : source.memory = InitE.sourceMemory
  domain : source.memaddrs = InitE.ordinaryDomain
  shared : source.shMemaddrs = InitE.sharedDomain
  little : source.be = false
  oracle : source.ffi.oracle = InitE.sourceOracle
  host : source.ffi.ffiState = Guest.guestHostMemory input
  heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word 0#64))
  scratch : source.globals.lookup (ofString "scratch_ptr") = some (.val (.word 0#64))
  frame : source.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word 0#64))

/-- Every actual terminating source observation reaches the literal main
body with its declaration-derived globals, domains and host state. -/
theorem reached (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source target result actualOutcome,
      Entry input source ∧ evaluateHOLFiniteState source body = (result,target) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  classical
  obtain ⟨structs,declared,clock,target,result,actualOutcome,_,declarations,code,shapes,metadata,run,classified,observation,_,_⟩ := SourceEntry.original_main input outcome events terminates
  obtain ⟨callee,called⟩ := nullary_environment declared.code.lookup (ofString "main") body (original_code declared.code code)
  have terminal : (∃ value,result = some (.returned value)) ∨ ∃ event,result = some (.finalFfi event) := by
    cases result with
    | none => cases classified
    | some result =>
      cases result with
      | returned value => exact Or.inl ⟨value,rfl⟩
      | finalFfi event => exact Or.inr ⟨event,rfl⟩
      | error | timeOut | «break» | «continue» | exception identifier payload => cases classified
  obtain ⟨_,bodyTarget,bodyRun,post⟩ := CallNormal.tail_terminating {declared with clock := clock} target (ofString "main") [] [] body callee .one rfl called result run terminal
  let source := callEntryStateHOLFinite {declared with clock := clock} callee
  have entry : Entry input source := {
    code := code
    shapes := shapes
    scalars := OriginalScalarGlobals.declaration_scalars _ declared declarations
    zeros := OriginalScalarGlobals.declaration_pass _ declared declarations
    base := congrArg (fun s => s.baseAddr) metadata
    memory := congrArg (fun s => s.memory) metadata
    domain := congrArg (fun s => s.memaddrs) metadata
    shared := congrArg (fun s => s.shMemaddrs) metadata
    little := congrArg (fun s => s.be) metadata
    oracle := congrArg (fun s => s.ffi.oracle) metadata
    host := congrArg (fun s => s.ffi.ffiState) metadata
    heap := OriginalArenaGlobals.declaration_pass _ declared declarations .heap
    scratch := OriginalArenaGlobals.declaration_pass _ declared declarations .scratch
    frame := OriginalArenaGlobals.declaration_pass _ declared declarations .frame }
  refine ⟨source,bodyTarget,result,actualOutcome,entry,bodyRun,classified,?_⟩
  rw [post] at observation
  exact observation

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.nullary_environment
#print axioms InitECandidate.Solver.Input.Main.reached
