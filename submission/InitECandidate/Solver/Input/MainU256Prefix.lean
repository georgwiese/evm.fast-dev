import InitECandidate.Solver.Input.MainMptPrefix
import InitECandidate.Solver.Input.MainU256Initialization

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def afterU256 : ProgHOL 64 := match afterMpt with | .seq _ rest => rest | _ => .skip
def u256State (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  {U256Initialization.template source 2713717640 with clock := source.clock - 2}

theorem u256_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    InitializerAllocations.context (u256State source) = InitializerAllocations.context source := by
  unfold u256State
  rw [InitializerAllocations.context_clock]
  exact InitializerAllocations.template_context source 2713717640 U256Initialization.actions

theorem u256_heap (source middle : PanSemStateFiniteExact 64 Guest.HostMemory) (reached : MptReached source middle) :
    (u256State middle).globals.lookup (ofString "heap_ptr") = some (.val (.word 2713718280#64)) :=
  InitializerAllocations.template_heap middle 2713717640 U256Initialization.actions (reached.heap source middle) U256Initialization.valid

theorem u256_scalars (input : Guest.InputBlob) (source middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (reached : MptReached source middle) : OriginalScalarGlobals.Scalars (u256State middle).globals :=
  InitializerAllocations.template_scalars middle 2713717640 U256Initialization.actions (reached.scalars input source middle entry)

theorem u256_spent (source middle : PanSemStateFiniteExact 64 Guest.HostMemory) (reached : MptReached source middle)
    (funded : 2 ≤ middle.clock) :
    (u256State middle).clock ≤ source.clock ∧ source.clock - (u256State middle).clock ≤ 426 := by
  have current : (u256State middle).clock = middle.clock - 2 := rfl
  have forward := reached.forward
  have spent := reached.spent
  rw [current]
  omega

theorem after_mpt_shape : afterMpt = .seq (.call (some (none,none)) (ofString "u256_ws_init") []) afterU256 := by
  simp only [afterMpt,afterSsz,afterKeccak,afterSha,afterMemory,body,afterU256,Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem workspace_before_u256 (input : Guest.InputBlob) (source middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (reached : MptReached source middle) :
    middle.globals.lookup (ofString "u256_ws") = some (.val (.word 0#64)) := by
  have globals := congrArg (fun s : PanSemStateFiniteExact 64 Guest.HostMemory => s.globals) reached.control
  change middle.globals = (MptInitialization.allocated (sszState source) 2713717456).globals at globals
  rw [globals]
  have mpt := MptInitialization.allocated_other (sszState source) 2713717456 (ofString "u256_ws") (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have ssz := SszInitialization.template_other (keccakState source) 2713715312 (ofString "u256_ws") (by decide) (by decide) (by decide) (by decide)
  have keccak := KeccakInitialization.template_other (shaState source) 2713714976 (ofString "u256_ws") (by decide) (by decide) (by decide)
  have sha := ShaInitialization.template_other (memoryState source) 2713714688 (ofString "u256_ws") (by decide) (by decide) (by decide) (by decide)
  have memory := memory_other source (ofString "u256_ws") (by decide) (by decide) (by decide)
  exact mpt.trans (ssz.trans (keccak.trans (sha.trans (memory.trans (entry.zeros _ U256Initialization.workspace_member)))))

theorem u256_prefix (input : Guest.InputBlob) (source middle post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (reached : MptReached source middle) (result : Option (PanSemResultExact 64))
    (normal : evaluateHOLFiniteState middle afterMpt = (result,post)) (notTimeout : result ≠ some .timeOut) :
    2 ≤ middle.clock ∧ evaluateHOLFiniteState (u256State middle) afterU256 = (result,post) := by
  have code := reached.code source middle
  have installed : OriginalCode.Installed middle.code := by rw [code]; exact entry.code
  have zero := workspace_before_u256 input source middle entry reached
  have execute (clock : Nat) (enough : 2 ≤ clock) :
      evaluateHOLFiniteState {middle with clock := clock} (.call (some (none,none)) (ofString "u256_ws_init") []) =
        (none,{U256Initialization.template middle 2713717640 with clock := clock - 2}) := by
    have current := U256Initialization.call_execute {middle with clock := clock} 2713717640 installed
      (reached.scalars input source middle entry) (reached.heap source middle) zero (by decide) (by decide) enough
    rw [U256Initialization.template,InitializerAllocations.template_clock] at current
    exact current
  rw [after_mpt_shape] at normal
  exact terminating_prefix middle post (U256Initialization.template middle 2713717640) _ afterU256 2 result execute normal notTimeout

theorem reached_u256 (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source middle target result actualOutcome,
      Entry input source ∧ MptReached source middle ∧ 2 ≤ middle.clock ∧
      evaluateHOLFiniteState (u256State middle) afterU256 = (result,target) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨source,middle,target,result,actualOutcome,entry,metadata,run,classified,observation⟩ := reached_mpt input outcome events terminates
  have notTimeout : result ≠ some .timeOut := by
    intro bad
    rw [bad] at classified
    cases classified
  obtain ⟨funded,remaining⟩ := u256_prefix input source middle target entry metadata result run notTimeout
  exact ⟨source,middle,target,result,actualOutcome,entry,metadata,funded,remaining,classified,observation⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.after_mpt_shape
#print axioms InitECandidate.Solver.Input.Main.u256_context
#print axioms InitECandidate.Solver.Input.Main.u256_heap
#print axioms InitECandidate.Solver.Input.Main.u256_scalars
#print axioms InitECandidate.Solver.Input.Main.u256_spent
#print axioms InitECandidate.Solver.Input.Main.workspace_before_u256
#print axioms InitECandidate.Solver.Input.Main.u256_prefix
#print axioms InitECandidate.Solver.Input.Main.reached_u256
