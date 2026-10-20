import InitECandidate.Solver.Input.MainKeccakPrefix
import InitECandidate.Solver.Input.MainSszInitialization

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def afterSsz : ProgHOL 64 := match afterKeccak with | .seq _ rest => rest | _ => .skip
def sszState (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  {SszInitialization.template (keccakState source) 2713715312 with clock := source.clock - 12}

theorem after_keccak_shape : afterKeccak = .seq (.call (some (none,none)) (ofString "ssz_init") []) afterSsz := by
  simp only [afterKeccak,afterSha,afterMemory,body,afterSsz,Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

theorem zero_hashes_before_ssz (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (entry : Entry input source) :
    (keccakState source).globals.lookup (ofString "zero_hashes") = some (.val (.word 0#64)) := by
  have keccak := KeccakInitialization.template_other (shaState source) 2713714976 (ofString "zero_hashes") (by decide) (by decide) (by decide)
  have sha := ShaInitialization.template_other (memoryState source) 2713714688 (ofString "zero_hashes") (by decide) (by decide) (by decide) (by decide)
  have memory := memory_other source (ofString "zero_hashes") (by decide) (by decide) (by decide)
  exact keccak.trans (sha.trans (memory.trans (entry.zeros (ofString "zero_hashes") OriginalScalarGlobals.ssz_names.2.2)))

/-- The actual fixed SSZ data writes are reached by every terminating main
execution, after deriving both their initial guard and all allocation room. -/
theorem ssz_prefix (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (result : Option (PanSemResultExact 64))
    (terminal : (∃ value,result = some (.returned value)) ∨ ∃ event,result = some (.finalFfi event))
    (normal : evaluateHOLFiniteState source body = (result,post)) :
    12 ≤ source.clock ∧ evaluateHOLFiniteState (sszState source) afterSsz = (result,post) := by
  obtain ⟨_,tailRun⟩ := keccak_prefix input source post entry result terminal normal
  let ready := keccakState source
  have notTimeout : result ≠ some .timeOut := by
    intro bad
    rcases terminal with ⟨value,same⟩ | ⟨event,same⟩ <;> rw [same] at bad <;> cases bad
  have shaScalars := ShaInitialization.template_scalars (memoryState source) 2713714688 (memory_scalars input source entry)
  have scalars : OriginalScalarGlobals.Scalars ready.globals := KeccakInitialization.template_scalars (shaState source) 2713714976 shaScalars
  have shaHeap := ShaInitialization.template_heap (memoryState source) 2713714688
  have heap : ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 2713715312))) :=
    KeccakInitialization.template_heap (shaState source) 2713714976 shaHeap
  have zero := zero_hashes_before_ssz input source entry
  have execute (clock : Nat) (funded : 4 ≤ clock) :
      evaluateHOLFiniteState {ready with clock := clock} (.call (some (none,none)) (ofString "ssz_init") []) =
        (none,{SszInitialization.template ready 2713715312 with clock := clock - 4}) := by
    have current := SszInitialization.call_execute {ready with clock := clock} 2713715312 entry.code scalars heap zero entry.domain (by decide) (by decide) (by decide) funded
    rw [SszInitialization.template_clock] at current
    exact current
  rw [after_keccak_shape] at tailRun
  obtain ⟨funded,remaining⟩ := terminating_prefix ready post (SszInitialization.template ready 2713715312) _ afterSsz 4 result execute tailRun notTimeout
  have positive : 12 ≤ source.clock := by change 4 ≤ source.clock - 8 at funded; omega
  have clock : source.clock - 8 - 4 = source.clock - 12 := by omega
  change evaluateHOLFiniteState {SszInitialization.template ready 2713715312 with clock := source.clock - 8 - 4} afterSsz = _ at remaining
  rw [clock] at remaining
  exact ⟨positive,remaining⟩

theorem reached_ssz (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source target result actualOutcome,
      Entry input source ∧ 12 ≤ source.clock ∧ evaluateHOLFiniteState (sszState source) afterSsz = (result,target) ∧
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
  obtain ⟨funded,remaining⟩ := ssz_prefix input source target entry result terminal run
  exact ⟨source,target,result,actualOutcome,entry,funded,remaining,classified,observation⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.after_keccak_shape
#print axioms InitECandidate.Solver.Input.Main.zero_hashes_before_ssz
#print axioms InitECandidate.Solver.Input.Main.ssz_prefix
#print axioms InitECandidate.Solver.Input.Main.reached_ssz
