import InitECandidate.Solver.Input.MainEntry
import InitECandidate.Solver.Input.InitializerAllocations

namespace InitECandidate.Solver.Input.Main.U256Initialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def body : ProgHOL 64 := match Guest.guestFn_u256_ws_init with | .function fn => progToHOL fn.body | _ => .skip
def actions : List InitializerAllocations.Action := [InitializerAllocations.constant "u256_ws" 640]
def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := InitializerAllocations.template source cursor actions

theorem body_shape : body = .seq (.ite (.cmp .equal (.var .global (ofString "u256_ws")) (.const 0#64))
    (InitializerAllocations.call (InitializerAllocations.constant "u256_ws" 640)) .skip) (.return (.const 0#64)) := by
  simp only [body,InitializerAllocations.call,InitializerAllocations.constant,Guest.guestFn_u256_ws_init,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

open scoped InitE.MetadataComputation InitE.NameComputation in
theorem workspace_member : ofString "u256_ws" ∈ OriginalScalarGlobals.names := by decide_cbv

theorem valid : ∀ action,action ∈ actions → InitializerAllocations.Valid action := by
  intro action member
  simp only [actions,List.mem_cons,List.not_mem_nil,or_false] at member
  subst action
  exact InitializerAllocations.valid_constant "u256_ws" 640 workspace_member (by decide) (by decide)

theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "u256_ws_init") = some ([],body,.one) := by
  have checked := OriginalCode.indexed code installed 32 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_u256_ws_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Guest.guestFn_u256_ws_init,shapeToHOL,List.map_cons,List.map_nil] using checked

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "u256_ws") = some (.val (.word 0#64)))
    (room : cursor + 640 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 1 ≤ source.clock) :
    evaluateHOLFiniteState source body = (some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite {template source cursor with clock := source.clock - 1}) := by
  have same : evaluateHOLFiniteState source body = evaluateHOLFiniteState source (InitializerAllocations.program actions) := by
    rw [body_shape]
    simp [actions,InitializerAllocations.program,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evalHOLExact,toExact,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [same]
  exact InitializerAllocations.execute source cursor actions installed scalars heap valid room aligned enough

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (zero : source.globals.lookup (ofString "u256_ws") = some (.val (.word 0#64)))
    (room : cursor + 640 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 2 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "u256_ws_init") []) = (none,{template source cursor with clock := source.clock - 2}) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup (ofString "u256_ws_init") body (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have run := execute entry cursor installed scalars heap zero room aligned (by change 1 ≤ source.clock - 1; omega)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "u256_ws_init") [] [] body callee .one (.val (.word 0#64))
    (emptyLocalsHOLFinite {template entry cursor with clock := entry.clock - 1}) rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  change evaluateHOLFiniteState source (.call (some (none,none)) (ofString "u256_ws_init") []) = (none,{template source cursor with clock := source.clock - 1 - 1}) at actual
  simpa only [Nat.sub_sub,show 1 + 1 = 2 from rfl] using actual

end InitECandidate.Solver.Input.Main.U256Initialization

#print axioms InitECandidate.Solver.Input.Main.U256Initialization.body_shape
#print axioms InitECandidate.Solver.Input.Main.U256Initialization.workspace_member
#print axioms InitECandidate.Solver.Input.Main.U256Initialization.valid
#print axioms InitECandidate.Solver.Input.Main.U256Initialization.original_code
#print axioms InitECandidate.Solver.Input.Main.U256Initialization.execute
#print axioms InitECandidate.Solver.Input.Main.U256Initialization.call_execute
