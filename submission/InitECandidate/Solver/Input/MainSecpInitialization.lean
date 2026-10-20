import InitECandidate.Solver.Input.MainSecpProgram

namespace InitECandidate.Solver.Input.Main.SecpInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

private theorem block_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64) (words : SecpBlock.Words) (clock : Nat) :
    SecpBlock.template {source with clock := clock} pointer words = {SecpBlock.template source pointer words with clock := clock} := rfl

private theorem block_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor offset : Nat) (words : SecpBlock.Words)
    (scratch : source.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word (BitVec.ofNat 64 cursor)))) :
    evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query))
      [.op .add [.var .global (ofString "secp_accel_scratch"),.const (BitVec.ofNat 64 offset)],quadExpression words] =
      some (SecpBlock.values (BitVec.ofNat 64 (cursor + offset)) words) := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,scratch,quadExpression,RlpWrite.U256Value.tuple,SecpBlock.values,
    valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]

/-- Full original first-time secp256k1 initialization: actual allocation,
both actual block calls, all sixteen stored words and the final return. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor)
    (room : cursor + 448 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 3 ≤ source.clock) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {template source cursor with clock := source.clock - 3}) := by
  have guardRun : evaluateHOLFiniteState source guard = (none,source) := by
    simp [guard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_skip,evalHOLExact,toExact,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have allocationRun := InitializerAllocations.execute_prefix source cursor actions afterAllocation installed scalars heap valid room aligned (by change 1 ≤ source.clock; omega)
  rw [body_shape,StateSteps.next_sequence source source guard _ guardRun (Nat.le_refl _),allocationRun]
  let ready := {allocated source cursor with clock := source.clock - 1}
  let firstState := SecpBlock.template (allocated source cursor) (BitVec.ofNat 64 cursor) prime
  let middle := {firstState with clock := source.clock - 2}
  let finished := {template source cursor with clock := source.clock - 3}
  have number (offset : Nat) (inside : offset ≤ 448) : (BitVec.ofNat 64 (cursor + offset)).toNat = cursor + offset := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have baseNumber : (BitVec.ofNat 64 cursor).toNat = cursor := by simpa using number 0 (by decide)
  have firstArena : AllocatedBytes.Arena (BitVec.ofNat 64 cursor) 128 := ⟨by rw [baseNumber]; exact lower,by rw [baseNumber]; omega⟩
  have nextArena : AllocatedBytes.Arena (BitVec.ofNat 64 (cursor + 160)) 128 := ⟨by rw [number 160 (by decide)]; omega,by rw [number 160 (by decide)]; omega⟩
  have firstArgs := block_arguments ready cursor 0 prime (allocated_scratch source cursor)
  have firstRun := SecpBlock.call_execute ready _ (BitVec.ofNat 64 cursor) prime firstArgs installed domain firstArena
    (by rw [baseNumber]; exact aligned) (by change 1 ≤ source.clock - 1; omega)
  change evaluateHOLFiniteState ready (blockCall 0 prime) = (none,{SecpBlock.template {allocated source cursor with clock := source.clock - 1} (BitVec.ofNat 64 cursor) prime with clock := source.clock - 1 - 1}) at firstRun
  rw [block_clock] at firstRun
  have clock2 : source.clock - 1 - 1 = source.clock - 2 := by omega
  rw [clock2] at firstRun
  have secondArgs := block_arguments middle cursor 160 order (allocated_scratch source cursor)
  have secondRun := SecpBlock.call_execute middle _ (BitVec.ofNat 64 (cursor + 160)) order secondArgs installed domain nextArena
    (by rw [number 160 (by decide)]; omega) (by change 1 ≤ source.clock - 2; omega)
  change evaluateHOLFiniteState middle (blockCall 160 order) = (none,{SecpBlock.template {firstState with clock := source.clock - 2} (BitVec.ofNat 64 (cursor + 160)) order with clock := source.clock - 2 - 1}) at secondRun
  rw [block_clock] at secondRun
  have clock3 : source.clock - 2 - 1 = source.clock - 3 := by omega
  rw [clock3] at secondRun
  change evaluateHOLFiniteState ready afterAllocation = _
  rw [afterAllocation,StateSteps.next_sequence ready middle _ _ firstRun (by change source.clock - 2 ≤ source.clock - 1; omega),
    StateSteps.next_sequence middle finished _ _ secondRun (by change source.clock - 3 ≤ source.clock - 2; omega)]
  exact BuildEntry.zero_return finished

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word 0#64)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (lower : 2701131776 ≤ cursor)
    (room : cursor + 448 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 4 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "secp256k1_init") []) = (none,{template source cursor with clock := source.clock - 4}) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup (ofString "secp256k1_init") body (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have run := execute entry cursor installed scalars heap zero domain lower room aligned (by change 3 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "secp256k1_init") [] [] body callee .one (.val (.word 0#64))
    (emptyLocalsHOLFinite {template entry cursor with clock := entry.clock - 3}) rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  change evaluateHOLFiniteState source (.call (some (none,none)) (ofString "secp256k1_init") []) = (none,{template source cursor with clock := source.clock - 1 - 3}) at actual
  simpa only [Nat.sub_sub,show 1 + 3 = 4 from rfl] using actual

end InitECandidate.Solver.Input.Main.SecpInitialization

#print axioms InitECandidate.Solver.Input.Main.SecpInitialization.execute
#print axioms InitECandidate.Solver.Input.Main.SecpInitialization.call_execute
