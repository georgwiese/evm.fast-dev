import InitECandidate.Solver.Input.MainBnAccelTailPlan

namespace InitECandidate.Solver.Input.Main.BnAccelInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

private theorem singleton_valid (action : InitializerAllocations.Action) (valid : InitializerAllocations.Valid action) :
    ∀ current,current ∈ [action] → InitializerAllocations.Valid current := by
  intro current member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  subst current
  exact valid

private theorem restore_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (temporary saved : HolFiniteMapExact MlS (ValueHOL 64)) (entryClock returnClock : Nat) :
    {emptyLocalsHOLFinite {{{source with locals := temporary} with clock := entryClock} with clock := returnClock} with locals := saved} =
      {{source with locals := saved} with clock := returnClock} := rfl

/-- All three real allocations, nine alias assignments and both actual
quad stores compose through the complete original accelerator initializer. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "bn_accel_params") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor)
    (room : cursor + 416 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 3 ≤ source.clock) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {template source cursor with clock := source.clock - 3}) := by
  have guardRun : evaluateHOLFiniteState source guard = (none,source) := by
    simp [guard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,toExact,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have firstAllocation := InitializerAllocations.execute_prefix source cursor [paramsAction] afterParamsAllocation installed scalars heap
    (singleton_valid paramsAction params_valid) (by change cursor + (160 + 0) ≤ 33806089496; omega) aligned (by change 1 ≤ source.clock; omega)
  simp only [List.length_cons,List.length_nil,Nat.zero_add] at firstAllocation
  have firstTail := params_tail {source with clock := source.clock - 1} cursor scalars domain lower room aligned
  conv_lhs at firstTail => rw [InitializerAllocations.template_clock]
  conv_rhs at firstTail => rw [seeded_clock]
  rw [body_shape,StateSteps.next_sequence source source guard _ guardRun (Nat.le_refl _),afterGuard,firstAllocation,firstTail]
  let seededReady := {seeded source cursor with clock := source.clock - 1}
  have seededInstalled := InitializerAllocations.installed_of_context source seededReady
    ((InitializerAllocations.context_clock (seeded source cursor) (source.clock - 1)).trans (seeded_context source cursor)) installed
  have seededGlobals : seededReady.globals = (params source cursor).globals := by
    simp only [seededReady,seeded,InitializerQuads.written_globals]
  have seededHeap : seededReady.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 160)))) := by
    rw [seededGlobals]
    exact params_heap source cursor
  have seededScalars : OriginalScalarGlobals.Scalars seededReady.globals := by
    rw [seededGlobals]
    exact params_scalars source cursor scalars
  have remaining := tail_execute seededReady cursor seededInstalled seededScalars seededHeap room aligned
    (by change 2 ≤ source.clock - 1; omega)
  have clock : source.clock - 1 - 2 = source.clock - 3 := by omega
  simp only [seededReady,InitializerAllocationAliases.template_clock,tail_template,clock] at remaining
  exact remaining

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "bn_accel_params") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor)
    (room : cursor + 416 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 4 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "bn254_accel_init") []) = (none,{template source cursor with clock := source.clock - 4}) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup (ofString "bn254_accel_init") body (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have run := execute entry cursor installed scalars heap zero domain lower room aligned (by change 3 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "bn254_accel_init") [] [] body callee .one (.val (.word 0#64))
    (emptyLocalsHOLFinite {template entry cursor with clock := entry.clock - 3}) rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  have entryFrame : entry = {{source with locals := callee} with clock := source.clock - 1} := rfl
  have unfolded := congrArg (fun s => template s cursor) entryFrame
  have commuteClock := template_clock {source with locals := callee} cursor (source.clock - 1)
  have commuteLocals := congrArg (fun s => {s with clock := source.clock - 1}) (template_locals source cursor callee)
  have frame := unfolded.trans (commuteClock.trans commuteLocals)
  rw [frame,restore_frame] at actual
  have restored : {template source cursor with locals := source.locals} = template source cursor := by
    rw [← template_locals_value source cursor]
  rw [restored] at actual
  have entryClock : entry.clock = source.clock - 1 := rfl
  rw [entryClock] at actual
  simpa only [Nat.sub_sub,show 1 + 3 = 4 from rfl] using actual

end InitECandidate.Solver.Input.Main.BnAccelInitialization

#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.execute
#print axioms InitECandidate.Solver.Input.Main.BnAccelInitialization.call_execute
