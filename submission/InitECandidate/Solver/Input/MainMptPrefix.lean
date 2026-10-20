import InitECandidate.Solver.Input.MainMptEntry
import InitECandidate.Solver.Input.MainMptInitialization
import InitECandidate.Solver.Input.TerminatingPaddedPrefix

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

private theorem hash_code (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (KeccakAbsorb.hashControl source).code = source.code := rfl

def afterMpt : ProgHOL 64 := match afterSsz with | .seq _ rest => rest | _ => .skip

theorem after_ssz_shape : afterSsz = .seq (.call (some (none,none)) (ofString "mpt_init") []) afterMpt := by
  simp only [afterSsz,afterKeccak,afterSha,afterMemory,body,afterMpt,Guest.guestFn_main,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none]

/-- Actual hash effects remain in the reached state; only their immutable
control fields coincide with the calculated allocation layout. -/
structure MptReached (source middle : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  forward : middle.clock ≤ source.clock
  spent : source.clock - middle.clock ≤ 424
  control : KeccakAbsorb.hashControl middle = KeccakAbsorb.hashControl (MptInitialization.allocated (sszState source) 2713717456)
  memory : ∀ query,Keccak256.Protected 2713714976#64 2713715176#64 2713717456#64 query →
    Keccak256.Protected 2713714976#64 2713715176#64 2713717488#64 query →
    query ≠ panByteAlignHOL (width := 64) 2713717584#64 → middle.memory query = (sszState source).memory query

theorem mpt_prefix (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (result : Option (PanSemResultExact 64))
    (terminal : (∃ value,result = some (.returned value)) ∨ ∃ event,result = some (.finalFfi event))
    (normal : evaluateHOLFiniteState source body = (result,post)) :
    ∃ middle,MptReached source middle ∧ evaluateHOLFiniteState middle afterMpt = (result,post) := by
  obtain ⟨initialCost,tailRun⟩ := ssz_prefix input source post entry result terminal normal
  let ready := sszState source
  let padded := {ready with clock := ready.clock + 412}
  have code : padded.code = source.code := ssz_code source
  have installed : OriginalCode.Installed padded.code := by rw [code]; exact entry.code
  have environment := ssz_hash_environment input source entry
  have paddedControl : KeccakAbsorb.hashControl padded = KeccakAbsorb.hashControl ready :=
    KeccakAbsorb.hashControl_clock ready padded.clock
  have paddedEnvironment : Keccak256.Environment padded 2713714976#64 2713715176#64 :=
    environment.of_control ready padded _ _ paddedControl
  obtain ⟨paddedMiddle,prefixRun,_,upper,bounded,control,frame⟩ := MptInitialization.call_execute padded 2713717456
    installed (ssz_scalars input source entry) (ssz_heap source) _ _ paddedEnvironment
    ⟨by decide,by decide⟩ (by decide) ⟨by decide,by decide⟩ (by decide)
    (by decide) (by decide) (by decide) (by change 412 ≤ ready.clock + 412; omega)
  have notTimeout : result ≠ some .timeOut := by
    intro bad
    rcases terminal with ⟨value,same⟩ | ⟨event,same⟩ <;> rw [same] at bad <;> cases bad
  rw [after_ssz_shape] at tailRun
  obtain ⟨funded,_,remaining⟩ := terminating_padded_prefix ready post paddedMiddle _ afterMpt 412 result prefixRun tailRun notTimeout
  refine ⟨{paddedMiddle with clock := paddedMiddle.clock - 412},?_,remaining⟩
  have currentClock : ready.clock = source.clock - 12 := rfl
  have upper' : paddedMiddle.clock ≤ ready.clock + 412 := upper
  have lower' : ready.clock ≤ paddedMiddle.clock := by
    change ready.clock + 412 - 412 ≤ paddedMiddle.clock at bounded
    simpa using bounded
  refine ⟨by change paddedMiddle.clock - 412 ≤ source.clock; omega,
    by change source.clock - (paddedMiddle.clock - 412) ≤ 424; omega,?_,frame⟩
  exact control.trans (InitializerAllocations.template_hash_control ready padded 2713717456 MptInitialization.actions paddedControl)

theorem MptReached.scalars (input : Guest.InputBlob) (source middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (reached : MptReached source middle) : OriginalScalarGlobals.Scalars middle.globals := by
  have globals := congrArg (fun s : PanSemStateFiniteExact 64 Guest.HostMemory => s.globals) reached.control
  change middle.globals = (MptInitialization.allocated (sszState source) 2713717456).globals at globals
  rw [globals]
  exact InitializerAllocations.template_scalars (sszState source) 2713717456 MptInitialization.actions (ssz_scalars input source entry)

theorem MptReached.heap (source middle : PanSemStateFiniteExact 64 Guest.HostMemory) (reached : MptReached source middle) :
    middle.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713717640#64)) := by
  have globals := congrArg (fun s : PanSemStateFiniteExact 64 Guest.HostMemory => s.globals) reached.control
  change middle.globals = (MptInitialization.allocated (sszState source) 2713717456).globals at globals
  rw [globals]
  exact InitializerAllocations.template_heap (sszState source) 2713717456 MptInitialization.actions (ssz_heap source) MptInitialization.valid

theorem MptReached.code (source middle : PanSemStateFiniteExact 64 Guest.HostMemory) (reached : MptReached source middle) :
    middle.code = source.code := by
  have actual : middle.code = (MptInitialization.allocated (sszState source) 2713717456).code :=
    (hash_code middle).symm.trans
      ((congrArg (fun s => s.code) reached.control).trans (hash_code (MptInitialization.allocated (sszState source) 2713717456)))
  have allocation : (MptInitialization.allocated (sszState source) 2713717456).code = (sszState source).code :=
    (InitializerAllocations.context_code (MptInitialization.allocated (sszState source) 2713717456)).symm.trans
      ((congrArg (fun s => s.code) (InitializerAllocations.template_context (sszState source) 2713717456 MptInitialization.actions)).trans
        (InitializerAllocations.context_code (sszState source)))
  exact actual.trans (allocation.trans (ssz_code source))

theorem reached_mpt (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source middle target result actualOutcome,
      Entry input source ∧ MptReached source middle ∧ evaluateHOLFiniteState middle afterMpt = (result,target) ∧
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
  obtain ⟨middle,metadata,remaining⟩ := mpt_prefix input source target entry result terminal run
  exact ⟨source,middle,target,result,actualOutcome,entry,metadata,remaining,classified,observation⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.after_ssz_shape
#print axioms InitECandidate.Solver.Input.Main.mpt_prefix
#print axioms InitECandidate.Solver.Input.Main.MptReached.scalars
#print axioms InitECandidate.Solver.Input.Main.MptReached.heap
#print axioms InitECandidate.Solver.Input.Main.MptReached.code
#print axioms InitECandidate.Solver.Input.Main.reached_mpt
