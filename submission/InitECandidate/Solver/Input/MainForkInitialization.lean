import InitECandidate.Solver.Input.MainForkTail

namespace InitECandidate.Solver.Input.Main.ForkInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def zeroTemplate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := InitializerZeroBuffer.template source cursor zeroAction
def precompileTemplate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := InitializerZeroBuffer.template (zeroTemplate source cursor) (cursor + 32) precompileAction
def actions := zeroAction :: precompileAction :: finalActions addresses
def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := InitializerAllocations.template source cursor actions

private theorem combine_actions (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    InitializerAllocations.template (InitializerAllocations.template (InitializerAllocations.template source cursor [zeroAction]) (cursor + 32) [precompileAction])
      (cursor + 392) (finalActions addresses) = template source cursor := by
  simp only [template,actions,InitializerAllocations.template,zeroAction,precompileAction,InitializerAllocations.constant,Nat.add_assoc]

theorem precompile_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    KeccakAbsorb.hashControl (precompileTemplate source cursor) =
      KeccakAbsorb.hashControl (InitializerAllocations.template (InitializerAllocations.template source cursor [zeroAction]) (cursor + 32) [precompileAction]) :=
  (InitializerZeroBuffer.template_control (zeroTemplate source cursor) (cursor + 32) precompileAction).trans
    (InitializerAllocations.template_hash_control (InitializerAllocations.template source cursor [zeroAction]) (zeroTemplate source cursor) (cursor + 32) [precompileAction]
      (InitializerZeroBuffer.template_control source cursor zeroAction))

/-- Complete original fork startup, including both real zero calls, all
seventeen indexed address writes, seven actual address helpers and four
signature word writers. The allowance includes each original caller. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 592 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 110 ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),post) ∧
      post.clock ≤ source.clock ∧ source.clock - 110 ≤ post.clock ∧ KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl (template source cursor) := by
  have firstRun := InitializerZeroBuffer.execute_prefix source cursor zeroAction afterZero installed scalars heap initial_valid.1 domain lower
    (by change cursor + 32 ≤ _; omega) aligned (by change 3 ≤ source.clock; omega)
  let first := {zeroTemplate source cursor with clock := source.clock - 3}
  have firstContext : InitializerAllocations.context first = InitializerAllocations.context source :=
    (InitializerAllocations.context_clock _ _).trans (InitializerZeroBuffer.template_context source cursor zeroAction)
  have firstInstalled := InitializerAllocations.installed_of_context source first firstContext installed
  have firstDomain := (InitializerAllocations.domain_of_context source first firstContext).trans domain
  have firstScalars : OriginalScalarGlobals.Scalars first.globals := InitializerAllocations.template_scalars source cursor [zeroAction] scalars
  have firstHeap : first.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 32)))) :=
    InitializerAllocations.template_heap source cursor [zeroAction] heap (by intro action member; have same := List.mem_singleton.mp member; subst action; exact initial_valid.1)
  have secondRun := InitializerZeroBuffer.execute_prefix first (cursor + 32) precompileAction afterPrecompile firstInstalled firstScalars firstHeap initial_valid.2.1 firstDomain
    (by omega) (by change cursor + 32 + 360 ≤ _; omega) (by omega) (by change 14 ≤ source.clock - 3; omega)
  let ready := {precompileTemplate source cursor with clock := source.clock - 17}
  have secondNormalized : evaluateHOLFiniteState first afterZero = evaluateHOLFiniteState ready afterPrecompile := by
    change evaluateHOLFiniteState first (InitializerZeroBuffer.program precompileAction afterPrecompile) = _
    rw [secondRun]
    congr 1
  have readyContext : InitializerAllocations.context ready = InitializerAllocations.context source :=
    (InitializerAllocations.context_clock _ _).trans ((InitializerZeroBuffer.template_context (zeroTemplate source cursor) (cursor + 32) precompileAction).trans
      (InitializerZeroBuffer.template_context source cursor zeroAction))
  have currentInstalled := InitializerAllocations.installed_of_context source ready readyContext installed
  have currentDomain := (InitializerAllocations.domain_of_context source ready readyContext).trans domain
  have currentScalars : OriginalScalarGlobals.Scalars ready.globals :=
    InitializerAllocations.template_scalars (zeroTemplate source cursor) (cursor + 32) [precompileAction] firstScalars
  have currentHeap : ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 392)))) := by
    have actual := InitializerAllocations.template_heap (zeroTemplate source cursor) (cursor + 32) [precompileAction] firstHeap
      (by intro action member; have same := List.mem_singleton.mp member; subst action; exact initial_valid.2.1)
    change (InitializerAllocations.template (zeroTemplate source cursor) (cursor + 32) [precompileAction]).globals.lookup (ofString "heap_ptr") = _
    simpa only [InitializerAllocations.totalBytes,precompileAction,Nat.add_zero,Nat.add_assoc] using actual
  have binding : ready.globals.lookup (ofString "precompile_addrs") = some (.val (.word (BitVec.ofNat 64 (cursor + 32)))) :=
    WordTableInitialization.allocated_binding (zeroTemplate source cursor) (cursor + 32) precompileAction
  have number : (BitVec.ofNat 64 (cursor + 32)).toNat = cursor + 32 := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have arena : AllocatedBytes.Arena (BitVec.ofNat 64 (cursor + 32)) 360 := ⟨by rw [number]; omega,by rw [number]; omega⟩
  obtain ⟨post,run,upper,bounded,control⟩ := loop_tail_execute ready (cursor + 392) (BitVec.ofNat 64 (cursor + 32)) currentInstalled currentScalars currentHeap binding currentDomain arena
    (by omega) (by omega) (by omega) (by change 93 ≤ source.clock - 17; omega)
  have actual : evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),post) := by
    rw [body_shape,firstRun]
    change evaluateHOLFiniteState first afterZero = _
    rw [secondNormalized]
    exact run
  have initialControl : KeccakAbsorb.hashControl ready = KeccakAbsorb.hashControl (precompileTemplate source cursor) := KeccakAbsorb.hashControl_clock (precompileTemplate source cursor) (source.clock - 17)
  have transported := InitializerAllocations.template_hash_control
    (InitializerAllocations.template (InitializerAllocations.template source cursor [zeroAction]) (cursor + 32) [precompileAction]) ready
    (cursor + 392) (finalActions addresses) (initialControl.trans (precompile_control source cursor))
  have model := control.trans transported
  rw [combine_actions source cursor] at model
  refine ⟨post,actual,?_,?_,model⟩
  · change post.clock ≤ source.clock - 17 at upper
    omega
  · change source.clock - 17 - 93 ≤ post.clock at bounded
    omega

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor) (room : cursor + 592 ≤ 33806089496)
    (aligned : cursor % 8 = 0) (enough : 111 ≤ source.clock) :
    ∃ post,evaluateHOLFiniteState source (.call (some (none,none)) (ofString "fork_init") []) = (none,post) ∧ post.locals = source.locals ∧
      post.clock ≤ source.clock ∧ source.clock - 111 ≤ post.clock ∧ KeccakAbsorb.hashControl post = KeccakAbsorb.hashControl (template source cursor) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup (ofString "fork_init") body (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨target,run,upper,bounded,control⟩ := execute entry cursor installed scalars heap domain lower room aligned (by change 110 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "fork_init") [] [] body callee .one (.val (.word 0#64)) target rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  have model := InitializerAllocations.template_hash_control source entry cursor actions (by rfl)
  refine ⟨{target with locals := source.locals},actual,rfl,?_,?_,control.trans model⟩
  · change target.clock ≤ source.clock
    change target.clock ≤ source.clock - 1 at upper
    omega
  · change source.clock - 111 ≤ target.clock
    change source.clock - 1 - 110 ≤ target.clock at bounded
    omega

end InitECandidate.Solver.Input.Main.ForkInitialization

#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.precompile_control
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.execute
#print axioms InitECandidate.Solver.Input.Main.ForkInitialization.call_execute
