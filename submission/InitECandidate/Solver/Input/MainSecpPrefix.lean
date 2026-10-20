import InitECandidate.Solver.Input.MainSecpEntry
import InitECandidate.Solver.Input.MainSecpInitialization

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def afterSecp : ProgHOL 64 := match afterU256 with | .seq _ rest => rest | _ => .skip
def secpState (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  {SecpInitialization.template (u256State source) 2713718280 with clock := source.clock - 6}

theorem after_u256_shape : afterU256 = .seq (.call (some (none,none)) (ofString "secp256k1_init") []) afterSecp := by
  simp only [afterU256,afterMpt,afterSsz,afterKeccak,afterSha,afterMemory,body,afterSecp,Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem secp_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    InitializerAllocations.context (secpState source) = InitializerAllocations.context source := by
  unfold secpState
  rw [InitializerAllocations.context_clock,SecpInitialization.template_context,u256_context]

theorem secp_heap (source middle : PanSemStateFiniteExact 64 Guest.HostMemory) (reached : MptReached source middle) :
    (secpState middle).globals.lookup (ofString "heap_ptr") = some (.val (.word 2713718728#64)) :=
  SecpInitialization.template_heap (u256State middle) 2713718280 (u256_heap source middle reached)

theorem secp_scalars (input : Guest.InputBlob) (source middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (reached : MptReached source middle) : OriginalScalarGlobals.Scalars (secpState middle).globals :=
  SecpInitialization.template_scalars (u256State middle) 2713718280 (u256_scalars input source middle entry reached)

theorem secp_spent (source middle : PanSemStateFiniteExact 64 Guest.HostMemory) (reached : MptReached source middle)
    (funded : 6 ≤ middle.clock) :
    (secpState middle).clock ≤ source.clock ∧ source.clock - (secpState middle).clock ≤ 430 := by
  have current : (secpState middle).clock = middle.clock - 6 := rfl
  have forward := reached.forward
  have spent := reached.spent
  rw [current]
  omega

theorem secp_prefix (input : Guest.InputBlob) (source middle post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (reached : MptReached source middle) (result : Option (PanSemResultExact 64))
    (normal : evaluateHOLFiniteState (u256State middle) afterU256 = (result,post)) (notTimeout : result ≠ some .timeOut) :
    6 ≤ middle.clock ∧ evaluateHOLFiniteState (secpState middle) afterSecp = (result,post) := by
  let ready := u256State middle
  have installed : OriginalCode.Installed ready.code := by rw [u256_code source middle reached]; exact entry.code
  have scalars := u256_scalars input source middle entry reached
  have heap := u256_heap source middle reached
  have zero := secp_scratch_before input source middle entry reached
  have domain := u256_domain input source middle entry reached
  have execute (clock : Nat) (enough : 4 ≤ clock) :
      evaluateHOLFiniteState {ready with clock := clock} (.call (some (none,none)) (ofString "secp256k1_init") []) =
        (none,{SecpInitialization.template ready 2713718280 with clock := clock - 4}) := by
    have current := SecpInitialization.call_execute {ready with clock := clock} 2713718280 installed scalars heap zero domain (by decide) (by decide) (by decide) enough
    rw [SecpInitialization.template_clock] at current
    exact current
  rw [after_u256_shape] at normal
  obtain ⟨funded,remaining⟩ := terminating_prefix ready post (SecpInitialization.template ready 2713718280) _ afterSecp 4 result execute normal notTimeout
  have positive : 6 ≤ middle.clock := by change 4 ≤ middle.clock - 2 at funded; omega
  have clock : middle.clock - 2 - 4 = middle.clock - 6 := by omega
  change evaluateHOLFiniteState {SecpInitialization.template ready 2713718280 with clock := middle.clock - 2 - 4} afterSecp = _ at remaining
  rw [clock] at remaining
  exact ⟨positive,remaining⟩

theorem reached_secp (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source middle target result actualOutcome,
      Entry input source ∧ MptReached source middle ∧ 6 ≤ middle.clock ∧
      evaluateHOLFiniteState (secpState middle) afterSecp = (result,target) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨source,middle,target,result,actualOutcome,entry,metadata,_,run,classified,observation⟩ := reached_u256 input outcome events terminates
  have notTimeout : result ≠ some .timeOut := by
    intro bad
    rw [bad] at classified
    cases classified
  obtain ⟨funded,remaining⟩ := secp_prefix input source middle target entry metadata result run notTimeout
  exact ⟨source,middle,target,result,actualOutcome,entry,metadata,funded,remaining,classified,observation⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.after_u256_shape
#print axioms InitECandidate.Solver.Input.Main.secp_context
#print axioms InitECandidate.Solver.Input.Main.secp_heap
#print axioms InitECandidate.Solver.Input.Main.secp_scalars
#print axioms InitECandidate.Solver.Input.Main.secp_spent
#print axioms InitECandidate.Solver.Input.Main.secp_prefix
#print axioms InitECandidate.Solver.Input.Main.reached_secp
