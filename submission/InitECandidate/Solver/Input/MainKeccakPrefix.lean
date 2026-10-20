import InitECandidate.Solver.Input.MainShaPrefix
import InitECandidate.Solver.Input.MainKeccakInitialization

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxHeartbeats 2000000

def afterKeccak : ProgHOL 64 := match afterSha with | .seq _ rest => rest | _ => .skip
def keccakState (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  {KeccakInitialization.template (shaState source) 2713714976 with clock := source.clock - 8}

theorem after_sha_shape : afterSha = .seq (.call (some (none,none)) (ofString "keccak_init") []) afterKeccak := by
  simp only [afterSha,afterMemory,body,afterKeccak,Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem keccak_prefix (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (result : Option (PanSemResultExact 64))
    (terminal : (∃ value,result = some (.returned value)) ∨ ∃ event,result = some (.finalFfi event))
    (normal : evaluateHOLFiniteState source body = (result,post)) :
    8 ≤ source.clock ∧ evaluateHOLFiniteState (keccakState source) afterKeccak = (result,post) := by
  obtain ⟨_,tailRun⟩ := sha_prefix input source post entry result terminal normal
  let ready := shaState source
  have notTimeout : result ≠ some .timeOut := by
    intro bad
    rcases terminal with ⟨value,same⟩ | ⟨event,same⟩ <;> rw [same] at bad <;> cases bad
  have scalars : OriginalScalarGlobals.Scalars ready.globals := ShaInitialization.template_scalars (memoryState source) 2713714688 (memory_scalars input source entry)
  have heap : ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 2713714976))) :=
    ShaInitialization.template_heap (memoryState source) 2713714688
  have execute (clock : Nat) (funded : 3 ≤ clock) :
      evaluateHOLFiniteState {ready with clock := clock} (.call (some (none,none)) (ofString "keccak_init") []) =
        (none,{KeccakInitialization.template ready 2713714976 with clock := clock - 3}) := by
    have current := KeccakInitialization.call_execute {ready with clock := clock} 2713714976 entry.code scalars heap (by decide) (by decide) funded
    rw [KeccakInitialization.template_clock] at current
    exact current
  rw [after_sha_shape] at tailRun
  obtain ⟨funded,remaining⟩ := terminating_prefix ready post (KeccakInitialization.template ready 2713714976) _ afterKeccak 3 result execute tailRun notTimeout
  have positive : 8 ≤ source.clock := by change 3 ≤ source.clock - 5 at funded; omega
  have clock : source.clock - 5 - 3 = source.clock - 8 := by omega
  change evaluateHOLFiniteState {KeccakInitialization.template ready 2713714976 with clock := source.clock - 5 - 3} afterKeccak = _ at remaining
  rw [clock] at remaining
  exact ⟨positive,remaining⟩

theorem reached_keccak (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source target result actualOutcome,
      Entry input source ∧ 8 ≤ source.clock ∧ evaluateHOLFiniteState (keccakState source) afterKeccak = (result,target) ∧
      (match result with
       | some (.finalFfi event) => actualOutcome = HolOutcome.ffiOutcome event
       | some (.returned _) => actualOutcome = HolOutcome.success
       | _ => False) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨source,target,result,actualOutcome,entry,run,classified,observation⟩ := reached input outcome events terminates
  have terminal : (∃ value,result = some (.returned value)) ∨ ∃ event,result = some (.finalFfi event) := by
    cases result with
    | none => cases classified
    | some result =>
      cases result with
      | returned value => exact Or.inl ⟨value,rfl⟩
      | finalFfi event => exact Or.inr ⟨event,rfl⟩
      | error | timeOut | «break» | «continue» | exception identifier payload => cases classified
  obtain ⟨funded,remaining⟩ := keccak_prefix input source target entry result terminal run
  exact ⟨source,target,result,actualOutcome,entry,funded,remaining,classified,observation⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.after_sha_shape
#print axioms InitECandidate.Solver.Input.Main.keccak_prefix
#print axioms InitECandidate.Solver.Input.Main.reached_keccak
