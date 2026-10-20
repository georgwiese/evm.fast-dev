import InitECandidate.Solver.Input.MainStartupTrace
import InitECandidate.Solver.Input.MainInputProgram
import InitECandidate.Solver.Input.BlobOversizeCall

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem input_oversize_stops (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ready : InputReady input source) (large : Guest.maxInputBytes < input.length % 2 ^ 64)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterFork = (result,target)) :
    target.clock ≤ source.clock ∧ source.clock - target.clock ≤ 2 ∧ ∀ value,result ≠ some (.returned value) := by
  obtain ⟨stopped,post,actual,notReturned,upper,cost⟩ := Blob.oversize_call source input (ofString "inp") Blob.returnShape afterInput ready.code ready.oracle ready.host ready.shared large
  rw [after_fork_shape] at run
  have same := actual.symm.trans run
  have states : post = target := congrArg Prod.snd same
  have results : some stopped = result := congrArg Prod.fst same
  refine ⟨states ▸ upper,states ▸ cost,?_⟩
  intro value bad
  exact notReturned value (Option.some.inj (results.trans bad))

/-- Entire original main, for every terminal outcome on an oversized encoded
length, spends at most834 source-body ticks. This includes all real startup
and the rejected input call, with no successful-trap or copy premise. -/
theorem oversized_main_cost (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (large : Guest.maxInputBytes < input.length % 2 ^ 64)
    (result : Option (PanSemResultExact 64))
    (terminal : (∃ value,result = some (.returned value)) ∨ ∃ event,result = some (.finalFfi event))
    (run : evaluateHOLFiniteState source body = (result,target)) :
    source.clock - target.clock ≤ 834 ∧ ∀ value,result ≠ some (.returned value) := by
  obtain ⟨mptMiddle,bnMiddle,evmMiddle,middle,_,_,_,fork,ready,remaining⟩ := startup_trace input source target entry result terminal run
  obtain ⟨forward,cost,notReturned⟩ := input_oversize_stops input middle target ready large result remaining
  have before := fork.spent
  have beforeForward := fork.forward
  exact ⟨by omega,notReturned⟩

/-- Connect the bounded rejection path to the challenge's actual source
observation, retaining the original main run and its complete FFI events. -/
theorem source_oversize_bound (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (large : Guest.maxInputBytes < input.length % 2 ^ 64)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source target result actualOutcome,Entry input source ∧ evaluateHOLFiniteState source body = (result,target) ∧
      source.clock - target.clock ≤ 834 ∧
      (∃ event,result = some (.finalFfi event) ∧ actualOutcome = HolOutcome.ffiOutcome event) ∧
      HolBehaviour.terminate outcome events = .terminate actualOutcome target.ffi.ioEvents := by
  obtain ⟨source,target,result,actualOutcome,entry,run,classified,observation⟩ := reached input outcome events terminates
  have terminal : (∃ value,result = some (.returned value)) ∨ ∃ event,result = some (.finalFfi event) := by
    cases result with
    | none => cases classified
    | some result =>
      cases result with
      | returned value => exact Or.inl ⟨value,rfl⟩
      | finalFfi event => exact Or.inr ⟨event,rfl⟩
      | _ => cases classified
  obtain ⟨cost,notReturned⟩ := oversized_main_cost input source target entry large result terminal run
  have final : ∃ event,result = some (.finalFfi event) ∧ actualOutcome = HolOutcome.ffiOutcome event := by
    rcases terminal with ⟨value,bad⟩ | ⟨event,same⟩
    · exact False.elim (notReturned value bad)
    · refine ⟨event,same,?_⟩
      simpa only [same] using classified
  exact ⟨source,target,result,actualOutcome,entry,run,cost,final,observation⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.input_oversize_stops
#print axioms InitECandidate.Solver.Input.Main.oversized_main_cost
#print axioms InitECandidate.Solver.Input.Main.source_oversize_bound
