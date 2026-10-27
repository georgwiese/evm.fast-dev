import InitECandidate.Solver.Input.MainEntry

namespace InitECandidate.Solver.Input.Main
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def memoryState (source : PanSemStateFiniteExact 64 Guest.HostMemory) := memoryReady {source with clock := source.clock - 1}

theorem memory_call (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (positive : 1 ≤ source.clock) :
    evaluateHOLFiniteState source (.call (some (none,none)) (ofString "mem_init") []) = (none,memoryState source) := by
  obtain ⟨callee,called⟩ := nullary_environment source.code.lookup (ofString "mem_init") memoryBody (memory_code source.code entry.code)
  have actual := evaluateHOLFiniteState_call_return_caller_locals source none (ofString "mem_init") [] [] memoryBody callee .one (.val (.word 0#64))
    (emptyLocalsHOLFinite (memoryReady (callEntryStateHOLFinite source callee))) rfl called (by omega)
    (memory_execute (callEntryStateHOLFinite source callee) 0#64 0#64 0#64 entry.heap entry.scratch entry.frame) (by simp [shapeOfHOLExact,shapeEqHOL])
  exact actual

/-- Actual termination forces main to pass the first call clock. Its reached
state is calculated from the three genuine arena-global assignments. -/
theorem memory_prefix (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (entry : Entry input source) (result : Option (PanSemResultExact 64))
    (terminal : (∃ value,result = some (.returned value)) ∨ ∃ event,result = some (.finalFfi event))
    (normal : evaluateHOLFiniteState source body = (result,post)) :
    1 ≤ source.clock ∧ evaluateHOLFiniteState (memoryState source) afterMemory = (result,post) := by
  have positive : 1 ≤ source.clock := by
    by_cases positive : 1 ≤ source.clock
    · exact positive
    have zero : source.clock = 0 := by omega
    obtain ⟨callee,called⟩ := nullary_environment source.code.lookup (ofString "mem_init") memoryBody (memory_code source.code entry.code)
    have timed := evaluateHOLFiniteState_call_clock_zero source (some (none,none)) (ofString "mem_init") [] [] memoryBody callee .one rfl called zero
    rw [body_shape,evaluateHOLFiniteState_seq_line780,timed] at normal
    have same := congrArg Prod.fst normal
    simp only at same
    rw [← same] at terminal
    rcases terminal with ⟨value,impossible⟩ | ⟨event,impossible⟩ <;> cases impossible
  refine ⟨positive,?_⟩
  rw [body_shape,WitnessRadix.StateSteps.next_sequence source (memoryState source) _ _ (memory_call input source entry positive) (by change source.clock - 1 ≤ source.clock; omega)] at normal
  exact normal

theorem memory_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (memoryState source).globals.lookup (ofString "heap_ptr") = some (.val (.word source.baseAddr)) ∧
    (memoryState source).globals.lookup (ofString "scratch_ptr") = some (.val (.word 2701127680#64)) ∧
    (memoryState source).globals.lookup (ofString "frame_mem_ptr") = some (.val (.word 2688618496#64)) := by
  simp [memoryState,memoryReady,setGlobalHOLFinite,HolFiniteMapExact.update,FUPDATE,
    show ofString "frame_mem_ptr" ≠ ofString "heap_ptr" by decide,show ofString "scratch_ptr" ≠ ofString "heap_ptr" by decide,
    show ofString "frame_mem_ptr" ≠ ofString "scratch_ptr" by decide]

theorem memory_scalars (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (entry : Entry input source) :
    OriginalScalarGlobals.Scalars (memoryState source).globals :=
  ((entry.scalars.update (ofString "heap_ptr") source.baseAddr).update (ofString "scratch_ptr") 2701127680#64).update (ofString "frame_mem_ptr") 2688618496#64

theorem memory_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key : MlS)
    (notHeap : key ≠ ofString "heap_ptr") (notScratch : key ≠ ofString "scratch_ptr") (notFrame : key ≠ ofString "frame_mem_ptr") :
    (memoryState source).globals.lookup key = source.globals.lookup key := by
  simp [memoryState,memoryReady,setGlobalHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm notHeap,Ne.symm notScratch,Ne.symm notFrame]

/-- A whole terminating source behavior, including any covered rejection,
has this actual initialized prefix and a remaining literal main execution.
The arbitrary input list is retained exactly. -/
theorem reached_memory (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (terminates : InitE.sourceBehaviour input = .terminate outcome events) :
    ∃ source target result actualOutcome,
      Entry input source ∧ 1 ≤ source.clock ∧
      (memoryState source).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 InitE.sourceBase))) ∧
      (memoryState source).globals.lookup (ofString "scratch_ptr") = some (.val (.word 2701127680#64)) ∧
      (memoryState source).globals.lookup (ofString "frame_mem_ptr") = some (.val (.word 2688618496#64)) ∧
      evaluateHOLFiniteState (memoryState source) afterMemory = (result,target) ∧
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
  obtain ⟨positive,tailRun⟩ := memory_prefix input source target entry result terminal run
  have globals := memory_globals source
  rw [entry.base] at globals
  exact ⟨source,target,result,actualOutcome,entry,positive,globals.1,globals.2.1,globals.2.2,tailRun,classified,observation⟩

end InitECandidate.Solver.Input.Main

#print axioms InitECandidate.Solver.Input.Main.memory_call
#print axioms InitECandidate.Solver.Input.Main.memory_prefix
#print axioms InitECandidate.Solver.Input.Main.memory_globals
#print axioms InitECandidate.Solver.Input.Main.reached_memory

#print axioms InitECandidate.Solver.Input.Main.memory_scalars
#print axioms InitECandidate.Solver.Input.Main.memory_other
