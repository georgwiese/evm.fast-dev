import InitECandidate.Solver.Input.MainEntry
import InitECandidate.Solver.Input.InitializerAllocations

namespace InitECandidate.Solver.Input.Main.KeccakInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def body : ProgHOL 64 := match Guest.guestFn_keccak_init with | .function fn => progToHOL fn.body | _ => .skip
def actions : List InitializerAllocations.Action := [InitializerAllocations.constant "keccak_st" 200,InitializerAllocations.constant "keccak_pad" 136]
def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := InitializerAllocations.template source cursor actions

theorem body_shape : body = InitializerAllocations.program actions := by
  simp only [body,actions,InitializerAllocations.program,InitializerAllocations.call,InitializerAllocations.constant,
    Guest.guestFn_keccak_init,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem valid : ∀ action,action ∈ actions → InitializerAllocations.Valid action := by
  intro action member
  change action ∈ [InitializerAllocations.constant "keccak_st" 200,InitializerAllocations.constant "keccak_pad" 136] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact InitializerAllocations.valid_constant "keccak_st" 200 OriginalScalarGlobals.keccak_names.1 (by decide) (by decide)
  · exact InitializerAllocations.valid_constant "keccak_pad" 136 OriginalScalarGlobals.keccak_names.2 (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "keccak_init") = some ([],body,.one) := by
  have checked := OriginalCode.indexed code installed 89 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_keccak_init) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,body,Guest.guestFn_keccak_init,shapeToHOL,List.map_cons,List.map_nil] using checked

theorem template_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor clock : Nat) :
    template {source with clock := clock} cursor = {template source cursor with clock := clock} :=
  InitializerAllocations.template_clock source cursor actions clock

theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat)
    (installed : OriginalCode.Installed source.code) (scalars : OriginalScalarGlobals.Scalars source.globals)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 cursor))))
    (room : cursor + 336 ≤ 33806089496) (aligned : cursor % 8 = 0) (enough : 3 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak_init") []) = (none,{template source cursor with clock := source.clock - 3}) := by
  obtain ⟨callee,called⟩ := Main.nullary_environment source.code.lookup (ofString "keccak_init") body (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  have run := InitializerAllocations.execute entry cursor actions installed scalars heap valid room aligned (by change 2 ≤ source.clock - 1; omega)
  rw [← body_shape] at run
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "keccak_init") [] [] body callee .one (.val (.word 0#64))
    (emptyLocalsHOLFinite {template entry cursor with clock := entry.clock - 2}) rfl called (by omega) run (by simp [shapeOfHOLExact,shapeEqHOL])
  change evaluateHOLFiniteState source (.call (some (none,none)) (ofString "keccak_init") []) = (none,{template source cursor with clock := source.clock - 1 - 2}) at actual
  simpa only [Nat.sub_sub,show 1 + 2 = 3 from rfl] using actual

end InitECandidate.Solver.Input.Main.KeccakInitialization

#print axioms InitECandidate.Solver.Input.Main.KeccakInitialization.body_shape
#print axioms InitECandidate.Solver.Input.Main.KeccakInitialization.valid
#print axioms InitECandidate.Solver.Input.Main.KeccakInitialization.original_code
#print axioms InitECandidate.Solver.Input.Main.KeccakInitialization.template_clock
#print axioms InitECandidate.Solver.Input.Main.KeccakInitialization.call_execute
