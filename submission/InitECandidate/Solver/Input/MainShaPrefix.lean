import InitECandidate.Solver.Input.MainShaInitialization
import InitECandidate.Solver.Input.TerminatingPrefixFunding

namespace InitECandidate.Solver.Input.Main
set_option maxHeartbeats 2000000
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def afterSha : ProgHOL 64 := match afterMemory with | .seq _ rest => rest | _ => .skip
def shaState (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  {ShaInitialization.template (memoryState source) 2713714688 with clock := source.clock - 5}

theorem after_memory_shape : afterMemory = .seq (.call (some (none,none)) (ofString "sha256_init") []) afterSha := by
  simp only [afterMemory,body,afterSha,Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

/-- The three actual SHA allocations are reached from literal main. Their
funding follows from the enclosing termination, including terminal FFI runs. -/
theorem sha_prefix (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (result : Option (PanSemResultExact 64))
    (terminal : (∃ value,result = some (.returned value)) ∨ ∃ event,result = some (.finalFfi event))
    (normal : evaluateHOLFiniteState source body = (result,post)) :
    5 ≤ source.clock ∧ evaluateHOLFiniteState (shaState source) afterSha = (result,post) := by
  obtain ⟨_,tailRun⟩ := memory_prefix input source post entry result terminal normal
  let ready := memoryState source
  have notTimeout : result ≠ some .timeOut := by
    intro bad
    rcases terminal with ⟨value,same⟩ | ⟨event,same⟩ <;> rw [same] at bad <;> cases bad
  have execute (clock : Nat) (funded : 4 ≤ clock) :
      evaluateHOLFiniteState {ready with clock := clock} (.call (some (none,none)) (ofString "sha256_init") []) =
        (none,{ShaInitialization.template ready 2713714688 with clock := clock - 4}) := by
    have current := ShaInitialization.call_execute {ready with clock := clock} 2713714688 entry.code (memory_scalars input source entry)
      (memory_globals source).1 (by decide) (by decide) funded
    rw [ShaInitialization.template_clock] at current
    exact current
  rw [after_memory_shape] at tailRun
  obtain ⟨funded,remaining⟩ := terminating_prefix ready post (ShaInitialization.template ready 2713714688) _ afterSha 4 result execute tailRun notTimeout
  have positive : 5 ≤ source.clock := by change 4 ≤ source.clock - 1 at funded; omega
  have clock : source.clock - 1 - 4 = source.clock - 5 := by omega
  change evaluateHOLFiniteState {ShaInitialization.template ready 2713714688 with clock := source.clock - 1 - 4} afterSha = _ at remaining
  rw [clock] at remaining
  exact ⟨positive,remaining⟩

theorem reached_sha (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source target result actualOutcome,
      Entry input source ∧ 5 ≤ source.clock ∧ evaluateHOLFiniteState (shaState source) afterSha = (result,target) ∧
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
  obtain ⟨funded,remaining⟩ := sha_prefix input source target entry result terminal run
  exact ⟨source,target,result,actualOutcome,entry,funded,remaining,classified,observation⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.after_memory_shape
#print axioms InitECandidate.Solver.Input.Main.sha_prefix
#print axioms InitECandidate.Solver.Input.Main.reached_sha
