import InitECandidate.Solver.Input.MainBlsFpTail
import InitECandidate.Solver.Input.MainBlsGuards

namespace InitECandidate.Solver.Input.Main.BlsInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem after_constants_template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    afterConstantsTemplate (constantsTemplate source cursor) (cursor + 7136) (BitVec.ofNat 64 cursor) = libTemplate source cursor := by
  unfold afterConstantsTemplate pairTemplate libTemplate fp2Template fpTemplate
  simp only [Nat.add_assoc]

/-- Complete original755 library setup. All four real helper calls execute;
current constants and remaining guards are derived from actual table effects. -/
theorem lib_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (constantsZero : source.globals.lookup (ofString "bls_c") = some (.val (.word 0#64)))
    (fpZero : source.globals.lookup (ofString "fp_accel_params") = some (.val (.word 0#64)))
    (fp2Zero : source.globals.lookup (ofString "fp2_accel_params") = some (.val (.word 0#64)))
    (g1Zero : source.globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 7760 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 19 ≤ source.clock) :
    evaluateHOLFiniteState source libBody = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {libTemplate source cursor with clock := source.clock - 19}) := by
  have constantsRun := BlsConstants.call_execute source cursor installed scalars heap constantsZero domain lower (by omega) aligned (by omega)
  let ready := {constantsTemplate source cursor with clock := source.clock - 2}
  have context : InitializerAllocations.context ready = InitializerAllocations.context source :=
    (InitializerAllocations.context_clock (constantsTemplate source cursor) (source.clock - 2)).trans (constants_context source cursor)
  have currentInstalled := InitializerAllocations.installed_of_context source ready context installed
  have currentDomain := (InitializerAllocations.domain_of_context source ready context).trans domain
  have globals : ready.globals = (constantsTemplate source cursor).globals := by simp only [ready]
  have currentScalars : OriginalScalarGlobals.Scalars ready.globals := by rw [globals]; exact constants_scalars source cursor scalars
  have currentHeap : ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 7136)))) := by rw [globals]; exact constants_heap source cursor heap
  have currentFp : ready.globals.lookup (ofString "fp_accel_params") = some (.val (.word 0#64)) := by rw [globals]; exact fp_zero source cursor fpZero
  have currentFp2 : ready.globals.lookup (ofString "fp2_accel_params") = some (.val (.word 0#64)) := by rw [globals]; exact (constants_other source cursor (ofString "fp2_accel_params") (by decide) (by decide)).trans fp2Zero
  have currentG1 : ready.globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0#64)) := by rw [globals]; exact (constants_other source cursor (ofString "bls_g1_accel_params") (by decide) (by decide)).trans g1Zero
  have currentConstants : ready.globals.lookup (ofString "bls_c") = some (.val (.word (BitVec.ofNat 64 cursor))) := by rw [globals]; exact constants_binding source cursor
  have number : (BitVec.ofNat 64 cursor).toNat = cursor := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have nonzero : BitVec.ofNat 64 cursor ≠ 0#64 := by intro zero; have same := congrArg BitVec.toNat zero; rw [number] at same; change cursor = 0 at same; omega
  have tailRun := fp_tail_execute ready (cursor + 7136) (BitVec.ofNat 64 cursor) currentInstalled currentScalars currentHeap currentFp currentFp2 currentG1 currentConstants nonzero currentDomain
    ⟨by rw [number]; exact lower,by rw [number]; omega⟩ (by rw [number]; exact aligned) (by omega) (by omega) (by omega) (by change 17 ≤ source.clock - 2; omega)
  rw [lib_body_shape,StateSteps.next_sequence source ready BlsPairInitialization.constantsCall _ constantsRun (by change source.clock - 2 ≤ source.clock; omega)]
  have clock : source.clock - 2 - 17 = source.clock - 19 := by omega
  simpa only [ready,after_constants_clock,after_constants_template,clock] using tailRun

private theorem constants_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    constantsTemplate {source with locals := locals} cursor = {constantsTemplate source cursor with locals := locals} := WordTableInitialization.template_locals source cursor BlsConstants.action BlsConstants.words locals

private theorem fp_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    fpTemplate {source with locals := locals} cursor = {fpTemplate source cursor with locals := locals} := by
  unfold fpTemplate
  rw [constants_locals source cursor locals]
  exact BlsFpInitialization.template_locals (constantsTemplate source cursor) (cursor + 7136) (BitVec.ofNat 64 cursor) locals

private theorem fp2_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    fp2Template {source with locals := locals} cursor = {fp2Template source cursor with locals := locals} := by
  unfold fp2Template
  rw [fp_locals source cursor locals]
  exact BlsPairInitialization.template_locals (fpTemplate source cursor) (cursor + 7376) .fp2 locals

theorem lib_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    libTemplate {source with locals := locals} cursor = {libTemplate source cursor with locals := locals} := by
  unfold libTemplate
  rw [fp2_locals source cursor locals]
  exact BlsPairInitialization.template_locals (fp2Template source cursor) (cursor + 7568) .g1 locals

theorem lib_locals_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) : (libTemplate source cursor).locals = source.locals := by
  have same : {source with locals := source.locals} = source := rfl
  have preserved := congrArg (fun state => state.locals) (lib_locals source cursor source.locals)
  rw [same] at preserved
  exact preserved

private theorem restore_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (temporary saved : HolFiniteMapExact MlS (ValueHOL 64)) (entryClock returnClock : Nat) :
    {emptyLocalsHOLFinite {{{source with locals := temporary} with clock := entryClock} with clock := returnClock} with locals := saved} =
      {{source with locals := saved} with clock := returnClock} := rfl

theorem lib_call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (constantsZero : source.globals.lookup (ofString "bls_c") = some (.val (.word 0#64)))
    (fpZero : source.globals.lookup (ofString "fp_accel_params") = some (.val (.word 0#64)))
    (fp2Zero : source.globals.lookup (ofString "fp2_accel_params") = some (.val (.word 0#64)))
    (g1Zero : source.globals.lookup (ofString "bls_g1_accel_params") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 7760 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 20 ≤ source.clock) :
    evaluateHOLFiniteState source libCall = (none,{libTemplate source cursor with clock := source.clock - 20}) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup (ofString "bls_lib_init") libBody (lib_original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have run := lib_execute entry cursor installed scalars heap constantsZero fpZero fp2Zero g1Zero domain lower room aligned (by change 19 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "bls_lib_init") [] [] libBody callee .one (.val (.word 0#64))
    (emptyLocalsHOLFinite {libTemplate entry cursor with clock := entry.clock - 19}) rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  have entryFrame : entry = {{source with locals := callee} with clock := source.clock - 1} := rfl
  have unfolded := congrArg (fun state => libTemplate state cursor) entryFrame
  have commuteClock := lib_clock {source with locals := callee} cursor (source.clock - 1)
  have commuteLocals := congrArg (fun state => {state with clock := source.clock - 1}) (lib_locals source cursor callee)
  have frame := unfolded.trans (commuteClock.trans commuteLocals)
  rw [frame,restore_frame] at actual
  have restored : {libTemplate source cursor with locals := source.locals} = libTemplate source cursor := by rw [← lib_locals_value source cursor]
  rw [restored] at actual
  have entryClock : entry.clock = source.clock - 1 := rfl
  rw [entryClock] at actual
  simpa only [libCall,Nat.sub_sub,show 1 + 19 = 20 from rfl] using actual

end InitECandidate.Solver.Input.Main.BlsInitialization

#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.after_constants_template
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.lib_execute
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.lib_locals
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.lib_locals_value
#print axioms InitECandidate.Solver.Input.Main.BlsInitialization.lib_call_execute
