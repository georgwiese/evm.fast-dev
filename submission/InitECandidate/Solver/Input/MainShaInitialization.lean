import InitECandidate.Solver.Input.MainMemoryPrefix
import InitECandidate.Solver.WitnessRadix.AllocationGlobalExecution
import InitECandidate.Solver.WitnessRadix.AllocationCost

namespace InitECandidate.Solver.Input.Main.ShaInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def body : ProgHOL 64 := match Guest.guestFn_sha256_init with | .function fn => progToHOL fn.body | _ => .skip
def allocate (name : String) (size : Nat) : ProgHOL 64 :=
  .call (some (some (.global,ofString name),none)) (ofString "alloc") [.const (BitVec.ofNat 64 size)]
def step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer next : Nat) :=
  putGlobal {source with globals := source.globals.update (ofString "heap_ptr",.val (.word (BitVec.ofNat 64 next))),clock := source.clock - 1} name (BitVec.ofNat 64 pointer)
def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :=
  {source with globals := (step (step (step source "sha_st" cursor (cursor + 64)) "sha_pad" (cursor + 64) (cursor + 192)) "sha_accel" (cursor + 192) (cursor + 288)).globals}

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    template {source with clock := clock} cursor = {template source cursor with clock := clock} := rfl

theorem body_shape : body = .seq (allocate "sha_st" 64) (.seq (allocate "sha_pad" 128) (.seq (allocate "sha_accel" 96) (.return (.const 0#64)))) := by
  simp only [body,allocate,Guest.guestFn_sha256_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "sha256_init") = some ([],body,.one) := by
  have checked := OriginalCode.indexed code installed 83 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_sha256_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Guest.guestFn_sha256_init,shapeToHOL,List.map_cons,List.map_nil] using checked

theorem step_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (pointer next : Nat)
    (scalars : OriginalScalarGlobals.Scalars source.globals) : OriginalScalarGlobals.Scalars (step source name pointer next).globals :=
  (scalars.update (ofString "heap_ptr") (BitVec.ofNat 64 next)).update (ofString name) (BitVec.ofNat 64 pointer)

theorem template_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (scalars : OriginalScalarGlobals.Scalars source.globals) : OriginalScalarGlobals.Scalars (template source cursor).globals :=
  step_scalars _ "sha_accel" (cursor + 192) (cursor + 288)
    (step_scalars _ "sha_pad" (cursor + 64) (cursor + 192) (step_scalars source "sha_st" cursor (cursor + 64) scalars))

theorem template_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (template source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 288)))) := by
  simp [template,step,putGlobal,HolFiniteMapExact.update,FUPDATE,show ofString "sha_accel" ≠ ofString "heap_ptr" by decide]

theorem template_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (key : MlS)
    (notHeap : key ≠ ofString "heap_ptr") (notState : key ≠ ofString "sha_st")
    (notPad : key ≠ ofString "sha_pad") (notAccel : key ≠ ofString "sha_accel") :
    (template source cursor).globals.lookup key = source.globals.lookup key := by
  simp [template,step,putGlobal,HolFiniteMapExact.update,FUPDATE,Ne.symm notHeap,Ne.symm notState,Ne.symm notPad,Ne.symm notAccel]

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (room : cursor + 288 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 3 ≤ source.clock) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {template source cursor with clock := source.clock - 3}) := by
  obtain ⟨oldSt,stPresent⟩ := scalars (ofString "sha_st") OriginalScalarGlobals.sha_names.1
  let first := step source "sha_st" cursor (cursor + 64)
  let second := step first "sha_pad" (cursor + 64) (cursor + 192)
  let last := step second "sha_accel" (cursor + 192) (cursor + 288)
  have firstRun := PersistentAlloc.global_call_execute_expected source "sha_st" oldSt cursor 64 (cursor + 64) (by omega) (Nat.le_refl _) (by omega) (by omega)
    stPresent [.const 64#64] rfl (PersistentAlloc.original_code source.code installed) heap (by omega)
  have firstScalars := step_scalars source "sha_st" cursor (cursor + 64) scalars
  obtain ⟨oldPad,padPresent⟩ := firstScalars (ofString "sha_pad") OriginalScalarGlobals.sha_names.2.1
  have firstHeap : first.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 64)))) := by
    simp [first,step,putGlobal,HolFiniteMapExact.update,FUPDATE,show ofString "sha_st" ≠ ofString "heap_ptr" by decide]
  have secondRun := PersistentAlloc.global_call_execute_expected first "sha_pad" oldPad (cursor + 64) 128 (cursor + 192) (by omega) (by omega) (by omega) (by omega)
    padPresent [.const 128#64] rfl (PersistentAlloc.original_code source.code installed) firstHeap (by change 1 ≤ source.clock - 1; omega)
  have secondScalars := step_scalars first "sha_pad" (cursor + 64) (cursor + 192) firstScalars
  obtain ⟨oldAccel,accelPresent⟩ := secondScalars (ofString "sha_accel") OriginalScalarGlobals.sha_names.2.2
  have secondHeap : second.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 192)))) := by
    simp [second,step,putGlobal,HolFiniteMapExact.update,FUPDATE,show ofString "sha_pad" ≠ ofString "heap_ptr" by decide]
  have thirdRun := PersistentAlloc.global_call_execute_expected second "sha_accel" oldAccel (cursor + 192) 96 (cursor + 288) room (by omega) (by omega) (by omega)
    accelPresent [.const 96#64] rfl (PersistentAlloc.original_code source.code installed) secondHeap (by change 1 ≤ source.clock - 1 - 1; omega)
  rw [body_shape]
  simp only [allocate]
  rw [StateSteps.next_sequence source first _ _ firstRun (by change source.clock - 1 ≤ source.clock; omega),
    StateSteps.next_sequence first second _ _ secondRun (by change source.clock - 1 - 1 ≤ source.clock - 1; omega),
    StateSteps.next_sequence second last _ _ thirdRun (by change source.clock - 1 - 1 - 1 ≤ source.clock - 1 - 1; omega)]
  have returned := BuildEntry.zero_return last
  have clock : source.clock - 1 - 1 - 1 = source.clock - 3 := by omega
  simpa only [last,second,first,step,putGlobal,template,clock,BuildEntry.returnZero] using returned

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (room : cursor + 288 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 4 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256_init") []) = (none,{template source cursor with clock := source.clock - 4}) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup (ofString "sha256_init") body (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have run := execute entry cursor installed scalars heap room aligned (by change 3 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "sha256_init") [] [] body callee .one (.val (.word 0#64))
    (emptyLocalsHOLFinite {template entry cursor with clock := entry.clock - 3}) rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  change evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256_init") []) = (none,{template source cursor with clock := source.clock - 1 - 3}) at actual
  simpa only [Nat.sub_sub,show 1 + 3 = 4 from rfl] using actual

end InitECandidate.Solver.Input.Main.ShaInitialization

#print axioms InitECandidate.Solver.Input.Main.ShaInitialization.body_shape
#print axioms InitECandidate.Solver.Input.Main.ShaInitialization.original_code
#print axioms InitECandidate.Solver.Input.Main.ShaInitialization.step_scalars
#print axioms InitECandidate.Solver.Input.Main.ShaInitialization.execute
#print axioms InitECandidate.Solver.Input.Main.ShaInitialization.call_execute
#print axioms InitECandidate.Solver.Input.Main.ShaInitialization.template_clock
#print axioms InitECandidate.Solver.Input.Main.ShaInitialization.template_scalars
#print axioms InitECandidate.Solver.Input.Main.ShaInitialization.template_heap
#print axioms InitECandidate.Solver.Input.Main.ShaInitialization.template_other
