import InitECandidate.Solver.Input.MainBnArithmetic
import InitECandidate.Solver.Input.MainBnStages
import InitECandidate.Solver.Input.BnEnvironmentFields

namespace InitECandidate.Solver.Input.Main.BnInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  InitializerAllocations.template (b2Allocated source cursor) (cursor + 864) [exponentAction]

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    template {source with clock := clock} cursor = {template source cursor with clock := clock} := by
  unfold template
  rw [b2_allocated_clock,InitializerAllocations.template_clock]

theorem template_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (scalars : OriginalScalarGlobals.Scalars source.globals) :
    OriginalScalarGlobals.Scalars (template source cursor).globals := InitializerAllocations.template_scalars _ _ _ (b2_scalars source cursor scalars)

theorem template_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (template source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 1216)))) := by
  simp only [template,InitializerAllocations.template_globals]
  simp [InitializerAllocations.globalTemplate,exponentAction,HolFiniteMapExact.update,FUPDATE,ofString,Nat.add_assoc]

/-- Complete first-time original BN254 initialization, retaining the actual
arithmetic events and table contents in its returned state. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (gammaZero : source.globals.lookup (ofString "bn_gamma") = some (.val (.word 0#64)))
    (paramsZero : source.globals.lookup (ofString "bn_accel_params") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (oracle : source.ffi.oracle = InitE.sourceOracle) (little : source.be = false)
    (lower : 2701131776 ≤ cursor) (room : cursor + 1216 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 16 ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),post) ∧
      post.clock ≤ source.clock ∧ source.clock - 16 ≤ post.clock ∧ KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl (template source cursor) := by
  have guardRun : evaluateHOLFiniteState source guard = (none,source) := by
    simp [guard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,toExact,gammaZero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have setup := setup_execute source cursor installed scalars heap paramsZero domain lower room aligned (by omega)
  let ready := {b2Allocated source cursor with clock := source.clock - 6}
  have current := b2_environment source cursor installed domain oracle little lower room aligned
  have currentEntry : BnModmul.Environment ready (BitVec.ofNat 64 cursor) := current.clock (b2Allocated source cursor) (BitVec.ofNat 64 cursor) (source.clock - 6)
  have number : (BitVec.ofNat 64 (cursor + 800)).toNat = cursor + 800 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  obtain ⟨post,run,upper,bounded,control⟩ := arithmetic_execute ready (BitVec.ofNat 64 cursor) (BitVec.ofNat 64 (cursor + 800)) (cursor + 864)
    currentEntry (b2_scalars source cursor scalars) (b2_heap source cursor) (b2_binding source cursor)
    ⟨by rw [number]; omega,by rw [number]; omega⟩ (by rw [number]; omega) (by omega) (by omega) (by omega) (by change 10 ≤ source.clock - 6; omega)
  refine ⟨post,?_,?_,?_,?_⟩
  · rw [body_shape,StateSteps.next_sequence source source guard afterGuard guardRun (Nat.le_refl _),setup]
    exact run
  · change post.clock ≤ source.clock - 6 at upper
    omega
  · change source.clock - 6 - 10 ≤ post.clock at bounded
    omega
  · exact control.trans (InitializerAllocations.template_hash_control (b2Allocated source cursor) ready (cursor + 864) [exponentAction] (KeccakAbsorb.hashControl_clock (b2Allocated source cursor) (source.clock - 6)))

private theorem gamma_allocated_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    gammaAllocated {source with locals := locals} cursor = {gammaAllocated source cursor with locals := locals} := by
  unfold gammaAllocated
  rw [BnAccelInitialization.template_locals source cursor locals]
  exact InitializerAllocations.template_locals (BnAccelInitialization.template source cursor) (cursor + 416) [gammaAction] locals

private theorem gamma_written_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    gammaWritten {source with locals := locals} cursor = {gammaWritten source cursor with locals := locals} := by
  unfold gammaWritten
  rw [gamma_allocated_locals source cursor locals]
  exact InitializerQuads.written_locals (gammaAllocated source cursor) (BitVec.ofNat 64 (cursor + 416)) 0 gamma locals

private theorem b2_allocated_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    b2Allocated {source with locals := locals} cursor = {b2Allocated source cursor with locals := locals} := by
  unfold b2Allocated
  rw [gamma_written_locals source cursor locals]
  exact InitializerAllocations.template_locals (gammaWritten source cursor) (cursor + 800) [b2Action] locals

theorem template_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    template {source with locals := locals} cursor = {template source cursor with locals := locals} := by
  unfold template
  rw [b2_allocated_locals source cursor locals]
  exact InitializerAllocations.template_locals (b2Allocated source cursor) (cursor + 864) [exponentAction] locals

private theorem erase_work (source : PanSemStateFiniteExact 64 Guest.HostMemory) (locals : HolFiniteMapExact MlS (ValueHOL 64)) (clock : Nat) :
    KeccakAbsorb.hashControl {{source with locals := locals} with clock := clock} = KeccakAbsorb.hashControl source := rfl

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (gammaZero : source.globals.lookup (ofString "bn_gamma") = some (.val (.word 0#64)))
    (paramsZero : source.globals.lookup (ofString "bn_accel_params") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (oracle : source.ffi.oracle = InitE.sourceOracle) (little : source.be = false)
    (lower : 2701131776 ≤ cursor) (room : cursor + 1216 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 17 ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source (.call (some (none,none)) (ofString "bn254_init") []) = (none,post) ∧ post.locals = source.locals ∧
      post.clock ≤ source.clock ∧ source.clock - 17 ≤ post.clock ∧ KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl (template source cursor) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup (ofString "bn254_init") body (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨target,run,upper,bounded,control⟩ := execute entry cursor installed scalars heap gammaZero paramsZero domain oracle little lower room aligned (by change 16 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "bn254_init") [] [] body callee .one (.val (.word 0#64)) target rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  have entryFrame : entry = {{source with locals := callee} with clock := source.clock - 1} := rfl
  have mapped := congrArg (fun state => template state cursor) entryFrame
  conv_rhs at mapped => rw [template_clock,template_locals]
  have entryControl : KeccakAbsorb.hashControl (template entry cursor) = KeccakAbsorb.hashControl (template source cursor) := by
    rw [mapped]
    exact erase_work (template source cursor) callee (source.clock - 1)
  refine ⟨{target with locals := source.locals},actual,rfl,?_,?_,control.trans entryControl⟩
  · change target.clock ≤ source.clock - 1 at upper
    change target.clock ≤ source.clock
    omega
  · change source.clock - 1 - 16 ≤ target.clock at bounded
    change source.clock - 17 ≤ target.clock
    omega

end InitECandidate.Solver.Input.Main.BnInitialization

#print axioms InitECandidate.Solver.Input.Main.BnInitialization.template_clock
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.template_scalars
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.template_heap
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.execute

#print axioms InitECandidate.Solver.Input.Main.BnInitialization.template_locals
#print axioms InitECandidate.Solver.Input.Main.BnInitialization.call_execute
