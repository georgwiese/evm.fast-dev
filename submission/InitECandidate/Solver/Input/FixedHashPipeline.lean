import InitECandidate.Solver.Input.FixedHashSteps
import InitECandidate.Solver.Input.IgnoredCallLookup
import InitECandidate.Solver.Input.ClockCostTerminatingSequence
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Input.FixedHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

structure Ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (inputName : String) (p ch out cursor mark stp accel chunk zeros : BitVec 64) : Prop where
  workspace : SszHash.Workspace source stp accel chunk zeros
  pointer : source.locals.lookup (ofString inputName)=some (.val (.word p))
  chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch))
  output : source.locals.lookup (ofString "out")=some (.val (.word out))
  saved : source.locals.lookup (ofString "mark")=some (.val (.word mark))
  heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor))

structure Geometry (p ch cursor : BitVec 64) (inputLength fields : Nat) : Prop where
  inputArena : AllocatedBytes.Arena p inputLength
  fieldArena : AllocatedBytes.Arena ch (32*fields)
  fieldAligned : ch.toNat%8=0
  arena : AllocatedBytes.Arena cursor 1120
  aligned : cursor.toNat%8=0

theorem Step.after (step : Step) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (inputName : String) (p ch out cursor mark stp accel chunk zeros : BitVec 64)
    (inputLength fields : Nat) (valid : step.Valid inputLength fields)
    (ready : Ready source inputName p ch out cursor mark stp accel chunk zeros) (geometry : Geometry p ch cursor inputLength fields)
    (run : evaluateHOLFiniteState source (step.program inputName)=(none,post)) : Ready post inputName p ch out cursor mark stp accel chunk zeros := by
  have summary := step.summary source post inputName p ch cursor stp accel chunk zeros inputLength fields valid ready.workspace ready.pointer ready.chunks ready.heap
    geometry.inputArena geometry.fieldArena geometry.fieldAligned geometry.arena geometry.aligned none run (by simp)
  have other (name : String) : post.locals.lookup (ofString name)=source.locals.lookup (ofString name) := CallNormal.ignored_lookup source post (ofString name) step.function (step.arguments inputName) run
  exact ⟨SszHash.Workspace.after source post stp accel chunk zeros ready.workspace _ none run (fun key different=>step.globals inputName key source.code ready.workspace.sha.installed different),
    (other inputName).trans ready.pointer,(other "ch").trans ready.chunks,(other "out").trans ready.output,(other "mark").trans ready.saved,summary.2 rfl⟩

/-- Real finite field pipelines retain a shared current state and charge
the sum of the actual scalar/vector/copy calls, including failed prefixes. -/
theorem pipeline_cost (steps : List Step) (inputName : String) (tail : ProgHOL 64) (tailPrice inputLength fields : Nat)
    (p ch out cursor mark stp accel chunk zeros : BitVec 64)
    (valid : ∀ step∈steps,step.Valid inputLength fields) (geometry : Geometry p ch cursor inputLength fields)
    (tailCost : ∀ source post : PanSemStateFiniteExact 64 Guest.HostMemory,Ready source inputName p ch out cursor mark stp accel chunk zeros → ∀ result,
      evaluateHOLFiniteState source tail=(result,post) → result≠some .timeOut → source.clock-post.clock≤tailPrice)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ready : Ready source inputName p ch out cursor mark stp accel chunk zeros)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (pipeline inputName steps tail)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤(steps.map Step.price).sum+tailPrice := by
  induction steps generalizing source post result with
  | nil=>simpa using tailCost source post ready result run notTimeout
  | cons step rest ih=>
    have stepValid := valid step (by simp)
    change evaluateHOLFiniteState source (.seq (step.program inputName) (pipeline inputName rest tail))=(result,post) at run
    have price := ClockCost.sequence_terminating source post _ _ step.price ((rest.map Step.price).sum+tailPrice)
      (by intro actual target evaluated notTimeout
          exact (step.summary source target inputName p ch cursor stp accel chunk zeros inputLength fields stepValid ready.workspace ready.pointer ready.chunks ready.heap
            geometry.inputArena geometry.fieldArena geometry.fieldAligned geometry.arena geometry.aligned actual evaluated notTimeout).1)
      (by intro middle normal actual target evaluated notTimeout
          exact ih (by intro next member; exact valid next (by simp [member])) middle target
            (step.after source middle inputName p ch out cursor mark stp accel chunk zeros inputLength fields stepValid ready geometry normal) actual evaluated notTimeout)
      result run notTimeout
    simpa only [List.map_cons,List.sum_cons,Nat.add_assoc] using price

/-- Normal pipeline return derives each intervening helper return from that
same execution before invoking the heap-restoring tail. -/
theorem pipeline_return_heap (steps : List Step) (inputName : String) (tail : ProgHOL 64) (inputLength fields : Nat)
    (p ch out cursor mark stp accel chunk zeros : BitVec 64)
    (valid : ∀ step∈steps,step.Valid inputLength fields) (geometry : Geometry p ch cursor inputLength fields)
    (tailHeap : ∀ source post : PanSemStateFiniteExact 64 Guest.HostMemory,Ready source inputName p ch out cursor mark stp accel chunk zeros → ∀ value,
      evaluateHOLFiniteState source tail=(some (.returned value),post) → post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)))
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ready : Ready source inputName p ch out cursor mark stp accel chunk zeros)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (pipeline inputName steps tail)=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  induction steps generalizing source post with
  | nil=>exact tailHeap source post ready value run
  | cons step rest ih=>
    have stepValid := valid step (by simp)
    change evaluateHOLFiniteState source (.seq (step.program inputName) (pipeline inputName rest tail))=(some (.returned value),post) at run
    have safe : LocalPrefix (ofString "mark") (step.program inputName) := .call none _ _ (by intro name impossible; cases impossible)
    obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ _ value (safe.summary_full source).2.1 run
    exact ih (by intro next member; exact valid next (by simp [member])) middle post
      (step.after source middle inputName p ch out cursor mark stp accel chunk zeros inputLength fields stepValid ready geometry normal) remaining

theorem pipeline_globals (steps : List Step) (inputName : String) (tail : ProgHOL 64) (key : MlS) (code) (installed : OriginalCode.Installed code)
    (different : key≠ofString "heap_ptr") (tailPure : GlobalEffects.Preserves key code tail) : GlobalEffects.Preserves key code (pipeline inputName steps tail) := by
  induction steps with
  | nil=>exact tailPure
  | cons step rest ih=>exact GlobalEffects.sequence key code _ _ (step.globals inputName key code installed different) ih

end InitECandidate.Solver.Input.FixedHash

#print axioms InitECandidate.Solver.Input.FixedHash.Step.after
#print axioms InitECandidate.Solver.Input.FixedHash.pipeline_cost
#print axioms InitECandidate.Solver.Input.FixedHash.pipeline_return_heap
#print axioms InitECandidate.Solver.Input.FixedHash.pipeline_globals
