import InitECandidate.Solver.Input.MainBlsLibInitialization

namespace InitECandidate.Solver.Input.Main.BlsInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  WordTableInitialization.template (libTemplate source cursor) (cursor + 7760) discountAction discountWords

private theorem guard_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (zero : source.globals.lookup (ofString "bls_discount") = some (.val (.word 0#64))) :
    evaluateHOLFiniteState source (WordTableInitialization.guard "bls_discount") = (none,source) := by
  simp [WordTableInitialization.guard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,toExact,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem discount_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "bls_discount") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 2048 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source afterLib = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {WordTableInitialization.template source cursor discountAction discountWords with clock := source.clock - 1}) := by
  have actual := WordTableInitialization.execute source cursor discountAction discountWords installed scalars heap zero discount_valid domain lower room aligned
    (by rw [discount_length]; rfl) enough
  change evaluateHOLFiniteState source (.seq (WordTableInitialization.guard "bls_discount") afterLib) = _ at actual
  rw [StateSteps.next_sequence source source _ _ (guard_zero source zero) (Nat.le_refl _)] at actual
  exact actual

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    template {source with clock := clock} cursor = {template source cursor with clock := clock} := by
  unfold template
  rw [lib_clock source cursor clock]
  exact WordTableInitialization.template_clock (libTemplate source cursor) (cursor + 7760) discountAction discountWords clock

theorem template_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    template {source with locals := locals} cursor = {template source cursor with locals := locals} := by
  unfold template
  rw [lib_locals source cursor locals]
  exact WordTableInitialization.template_locals (libTemplate source cursor) (cursor + 7760) discountAction discountWords locals

theorem template_locals_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) : (template source cursor).locals = source.locals := by
  unfold template
  rw [WordTableInitialization.template_locals_value,lib_locals_value]

theorem template_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.context (template source cursor) = InitializerAllocations.context source :=
  (WordTableInitialization.template_context (libTemplate source cursor) (cursor + 7760) discountAction discountWords).trans (lib_context source cursor)

theorem template_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (scalars : OriginalScalarGlobals.Scalars source.globals) :
    OriginalScalarGlobals.Scalars (template source cursor).globals :=
  WordTableInitialization.template_scalars (libTemplate source cursor) (cursor + 7760) discountAction discountWords (lib_scalars source cursor scalars)

theorem template_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor)))) :
    (template source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 9808)))) := by
  simpa only [template,discountAction,Nat.add_assoc,show 7760 + 2048 = 9808 from rfl] using WordTableInitialization.template_heap (libTemplate source cursor) (cursor + 7760) discountAction discountWords (lib_heap source cursor heap) discount_valid

/-- Complete original764 BLS startup, retaining all original table values,
zero/copy effects and actual globals. No helper success is an entry premise. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (discountZero : source.globals.lookup (ofString "bls_discount") = some (.val (.word 0#64)))
    (constantsZero : source.globals.lookup (ofString "bls_c") = some (.val (.word 0#64)))
    (fpZero : source.globals.lookup (ofString "fp_accel_params") = some (.val (.word 0#64)))
    (fp2Zero : source.globals.lookup (ofString "fp2_accel_params") = some (.val (.word 0#64)))
    (g1Zero : source.globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 9808 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 21 ≤ source.clock) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {template source cursor with clock := source.clock - 21}) := by
  have library := lib_call_execute source cursor installed scalars heap constantsZero fpZero fp2Zero g1Zero domain lower (by omega) aligned (by omega)
  let ready := {libTemplate source cursor with clock := source.clock - 20}
  have context : InitializerAllocations.context ready = InitializerAllocations.context source :=
    (InitializerAllocations.context_clock (libTemplate source cursor) (source.clock - 20)).trans (lib_context source cursor)
  have currentInstalled := InitializerAllocations.installed_of_context source ready context installed
  have currentDomain := (InitializerAllocations.domain_of_context source ready context).trans domain
  have globals : ready.globals = (libTemplate source cursor).globals := by simp only [ready]
  have currentScalars : OriginalScalarGlobals.Scalars ready.globals := by rw [globals]; exact lib_scalars source cursor scalars
  have currentHeap : ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 7760)))) := by rw [globals]; exact lib_heap source cursor heap
  have currentZero : ready.globals.lookup (ofString "bls_discount") = some (.val (.word 0#64)) := by rw [globals]; exact discount_zero source cursor discountZero
  have tailRun := discount_execute ready (cursor + 7760) currentInstalled currentScalars currentHeap currentZero currentDomain (by omega) (by omega) (by omega) (by change 1 ≤ source.clock - 20; omega)
  rw [body_shape,StateSteps.next_sequence source source _ _ (guard_zero source discountZero) (Nat.le_refl _),afterGuard,
    StateSteps.next_sequence source ready libCall _ library (by change source.clock - 20 ≤ source.clock; omega)]
  have clock : source.clock - 20 - 1 = source.clock - 21 := by omega
  simpa only [ready,WordTableInitialization.template_clock,clock,template] using tailRun

private theorem restore_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (temporary saved : HolFiniteMapExact MlS (ValueHOL 64)) (entryClock returnClock : Nat) :
    {emptyLocalsHOLFinite {{{source with locals := temporary} with clock := entryClock} with clock := returnClock} with locals := saved} =
      {{source with locals := saved} with clock := returnClock} := rfl

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (discountZero : source.globals.lookup (ofString "bls_discount") = some (.val (.word 0#64)))
    (constantsZero : source.globals.lookup (ofString "bls_c") = some (.val (.word 0#64)))
    (fpZero : source.globals.lookup (ofString "fp_accel_params") = some (.val (.word 0#64)))
    (fp2Zero : source.globals.lookup (ofString "fp2_accel_params") = some (.val (.word 0#64)))
    (g1Zero : source.globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 9808 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 22 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "bls_precompiles_init") []) = (none,{template source cursor with clock := source.clock - 22}) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup (ofString "bls_precompiles_init") body (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have run := execute entry cursor installed scalars heap discountZero constantsZero fpZero fp2Zero g1Zero domain lower room aligned (by change 21 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "bls_precompiles_init") [] [] body callee .one (.val (.word 0#64))
    (emptyLocalsHOLFinite {template entry cursor with clock := entry.clock - 21}) rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  have entryFrame : entry = {{source with locals := callee} with clock := source.clock - 1} := rfl
  have unfolded := congrArg (fun state => template state cursor) entryFrame
  have commuteClock := template_clock {source with locals := callee} cursor (source.clock - 1)
  have commuteLocals := congrArg (fun state => {state with clock := source.clock - 1}) (template_locals source cursor callee)
  have frame := unfolded.trans (commuteClock.trans commuteLocals)
  rw [frame,restore_frame] at actual
  have restored : {template source cursor with locals := source.locals} = template source cursor := by rw [← template_locals_value source cursor]
  rw [restored] at actual
  have entryClock : entry.clock = source.clock - 1 := rfl
  rw [entryClock] at actual
  simpa only [Nat.sub_sub,show 1 + 21 = 22 from rfl] using actual

end InitECandidate.Solver.Input.Main.BlsInitialization

#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.discount_execute
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.template_clock
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.template_locals
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.template_locals_value
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.template_context
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.template_scalars
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.template_heap
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.execute
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.call_execute
