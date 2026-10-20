import InitECandidate.Solver.Input.MainBnAccelLayout

namespace InitECandidate.Solver.Input.Main.BnAccelInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

private theorem allocated_binding (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (action : InitializerAllocations.Action) :
    (InitializerAllocations.template source cursor [action]).globals.lookup (ofString action.name) = some (.val (.word (BitVec.ofNat 64 cursor))) := by
  rw [InitializerAllocations.template_globals]
  simp [InitializerAllocations.globalTemplate,HolFiniteMapExact.update,FUPDATE]

/-- Both real tuple stores resume the literal suffix from a current layout.
The enclosing alias proof derives this layout from actual assignments. -/
theorem stores_tail (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (model : ParamsGlobals source cursor) (domain : source.memaddrs = InitE.ordinaryDomain)
    (lower : 2701131776 ≤ cursor) (room : cursor + 416 ≤ 33806089496) (aligned : cursor % 8 = 0) :
    evaluateHOLFiniteState source afterParamsAliases =
      evaluateHOLFiniteState (InitializerQuads.written (InitializerQuads.written source (BitVec.ofNat 64 (cursor + 64)) 0 [zeros])
        (BitVec.ofNat 64 (cursor + 96)) 0 [modulus]) afterModulus := by
  have number (offset : Nat) (inside : offset ≤ 416) : (BitVec.ofNat 64 (cursor + offset)).toNat = cursor + offset := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have zeroArena : AllocatedBytes.Arena (BitVec.ofNat 64 (cursor + 64)) 32 :=
    ⟨by rw [number 64 (by decide)]; omega,by rw [number 64 (by decide)]; omega⟩
  have modulusArena : AllocatedBytes.Arena (BitVec.ofNat 64 (cursor + 96)) 32 :=
    ⟨by rw [number 96 (by decide)]; omega,by rw [number 96 (by decide)]; omega⟩
  have first := InitializerQuads.execute source "bn_accel_zero" (BitVec.ofNat 64 (cursor + 64)) 0 32 [zeros] afterZero model.zero domain zeroArena
    (by rw [number 64 (by decide)]; omega) (by decide) (by decide)
  let zeroed := InitializerQuads.written source (BitVec.ofNat 64 (cursor + 64)) 0 [zeros]
  have modulusBinding : zeroed.globals.lookup (ofString "bn_accel_m") = some (.val (.word (BitVec.ofNat 64 (cursor + 96)))) := by
    rw [InitializerQuads.written_globals]
    exact model.modulus
  have zeroedDomain := (InitializerAllocations.domain_of_context source zeroed (InitializerQuads.written_context source _ _ _)).trans domain
  have second := InitializerQuads.execute zeroed "bn_accel_m" (BitVec.ofNat 64 (cursor + 96)) 0 32 [modulus] afterModulus modulusBinding zeroedDomain modulusArena
    (by rw [number 96 (by decide)]; omega) (by decide) (by decide)
  unfold afterParamsAliases
  rw [first]
  unfold afterZero
  exact second

/-- The actual first alias block derives the current layout and executes
both stores; no helper run or later state is an entry premise. -/
theorem params_tail (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (scalars : OriginalScalarGlobals.Scalars source.globals) (domain : source.memaddrs = InitE.ordinaryDomain)
    (lower : 2701131776 ≤ cursor) (room : cursor + 416 ≤ 33806089496) (aligned : cursor % 8 = 0) :
    evaluateHOLFiniteState (InitializerAllocations.template source cursor [paramsAction]) afterParamsAllocation =
      evaluateHOLFiniteState (seeded source cursor) afterModulus := by
  have aliasesRun := InitializerAliases.execute_prefix (InitializerAllocations.template source cursor [paramsAction]) "bn_accel_params" (BitVec.ofNat 64 cursor)
    paramsAliases afterParamsAliases (InitializerAllocations.template_scalars source cursor [paramsAction] scalars) (allocated_binding source cursor paramsAction) params_aliases_valid
  have currentDomain := (InitializerAllocations.domain_of_context source (params source cursor) (params_context source cursor)).trans domain
  have stored := stores_tail (params source cursor) cursor (params_bindings source cursor) currentDomain lower room aligned
  unfold afterParamsAllocation seeded
  rw [aliasesRun]
  exact stored

private theorem params_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    params {source with locals := locals} cursor = {params source cursor with locals := locals} := by
  unfold params
  rw [InitializerAllocations.template_locals,InitializerAliases.template_locals]

private theorem seeded_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    seeded {source with locals := locals} cursor = {seeded source cursor with locals := locals} := by
  unfold seeded
  simp only [params_locals,InitializerQuads.written_locals]

private theorem fp2_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    fp2 {source with locals := locals} cursor = {fp2 source cursor with locals := locals} := by
  unfold fp2
  rw [seeded_locals,InitializerAllocations.template_locals,InitializerAliases.template_locals]

theorem template_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (locals : HolFiniteMapExact MlS (ValueHOL 64)) :
    template {source with locals := locals} cursor = {template source cursor with locals := locals} := by
  unfold template
  rw [fp2_locals,InitializerAllocations.template_locals,InitializerAliases.template_locals]

theorem template_locals_value (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (template source cursor).locals = source.locals := by
  have same : {source with locals := source.locals} = source := rfl
  have preserved := congrArg (fun s => s.locals) (template_locals source cursor source.locals)
  rw [same] at preserved
  exact preserved

/-- Subsequent real initialization calls return immediately from the actual
nonzero guard, preserving all memory, globals and accumulated events. -/
theorem initialized_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (binding : source.globals.lookup (ofString "bn_accel_params") = some (.val (.word pointer))) (nonzero : pointer ≠ 0#64) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite source) := by
  have guardRun : evaluateHOLFiniteState source guard = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite source) := by
    have returned := BuildEntry.zero_return source
    simp only [BuildEntry.returnZero] at returned
    simp [guard,evaluateHOLFiniteState_ite,evalHOLExact,toExact,binding,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,nonzero,returned]
  rw [body_shape,evaluateHOLFiniteState_seq_line780,guardRun]

theorem initialized_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (binding : source.globals.lookup (ofString "bn_accel_params") = some (.val (.word pointer))) (nonzero : pointer ≠ 0#64) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "bn254_accel_init") []) = (none,{source with clock := source.clock - 1}) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup (ofString "bn254_accel_init") body (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have run := initialized_execute entry pointer binding nonzero
  exact evaluateHOLFiniteState_call_return_caller_locals source none (ofString "bn254_accel_init") [] [] body callee .one (.val (.word 0#64))
    (emptyLocalsHOLFinite entry) rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])

end InitECandidate.Solver.Input.Main.BnAccelInitialization

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.params_tail
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.template_locals
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.template_locals_value
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.initialized_execute
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.initialized_call

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.stores_tail
