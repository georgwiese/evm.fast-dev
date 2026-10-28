import InitECandidate.Solver.Input.CurrentHash.FixedRecordSteps
import InitECandidate.Solver.Input.CurrentHash.BytesCallMemory
import InitECandidate.Solver.Input.CurrentHash.MemoryContextTransport
import InitECandidate.Solver.Input.CurrentHash.U64Memory

namespace InitECandidate.Solver.Input.CurrentHash.FixedRecord
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def Step.routine : Step→Code.Routine
  | .scalar _ _=>.htr_u64_at | .copy _ _=>.memcpy | .vector _ _ _ _=>.htr_bytes_vector

theorem Step.function_name (step : Step) : step.function=Code.name step.routine := by cases step <;> rfl

/-- Each real fixed-record field call writes only its selected output slot
and restores the current heap. Its actual decoded input extent is explicit. -/
theorem Step.frame (step : Step) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (inputName : String) (p ch cursor zeros query : BitVec 64) (valid : step.Valid)
    (context : MerkleMemory.Context source cursor zeros query)
    (pointer : source.locals.lookup (ofString inputName)=some (.val (.word p)))
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (inputArena : AllocatedBytes.Arena (p+BitVec.ofNat 64 step.inputOffset) step.length)
    (outArena : AllocatedBytes.Arena (ch+BitVec.ofNat 64 (32*step.field)) 32)
    (outAligned : (ch+BitVec.ofNat 64 (32*step.field)).toNat%8=0)
    (outAway : CopyGeneral.Away (ch+BitVec.ofNat 64 (32*step.field)) query 32)
    (actual : evaluateHOLFiniteState source (step.program inputName)=(none,post)) :
    post.memory query=source.memory query ∧ MerkleMemory.Context post cursor zeros query := by
  have args := step.arguments_read source inputName p ch pointer chunks
  have frame : post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
    cases step with
    | scalar offset field =>
      have memory := U64Memory.call_memory source post (p+BitVec.ofNat 64 offset) (ch+BitVec.ofNat 64 (32*field)) query context.installed context.domain
        inputArena outArena outAligned outAway _ args actual
      have globals := GlobalEffects.call_body (ofString "heap_ptr") source.code (some none) (Code.name .htr_u64_at) ((Step.scalar offset field).arguments inputName)
        (Code.formals .htr_u64_at) (Code.body .htr_u64_at) (Code.shape .htr_u64_at) (Code.installed source.code context.installed .htr_u64_at)
        (PureGlobals.u64 _ source.code context.installed) source rfl
      change GlobalEffects.erase (ofString "heap_ptr") (evaluateHOLFiniteState source ((Step.scalar offset field).program inputName)).2 = _ at globals
      rw [actual] at globals
      exact ⟨memory,(congrArg Prod.snd globals).trans context.heap⟩
    | copy offset field =>
      have memory := MemoryAt.copy_normal source post _ (p+BitVec.ofNat 64 offset) (ch+BitVec.ofNat 64 (32*field)) query 32 args context.installed context.domain
        inputArena outArena outAway actual
      have globals := MemoryGlobals.call .copy (ofString "heap_ptr") source.code context.installed (some none) ((Step.copy offset field).arguments inputName) source rfl
      change GlobalEffects.erase (ofString "heap_ptr") (evaluateHOLFiniteState source ((Step.copy offset field).program inputName)).2 = _ at globals
      rw [actual] at globals
      exact ⟨memory,(congrArg Prod.snd globals).trans context.heap⟩
    | vector offset length field depth =>
      exact BytesCallMemory.frame .vector source post (p+BitVec.ofNat 64 offset) cursor 0#64 (ch+BitVec.ofNat 64 (32*field)) zeros 0#64 query length depth context
        valid.1 valid.2.1 valid.2.2 (by intro impossible; cases impossible) inputArena outArena (by intro; exact outAligned) outAway
        (by intro impossible; cases impossible) _ args actual
  refine ⟨frame.1,?_⟩
  unfold Step.program at actual
  rw [step.function_name] at actual
  exact context.after_call step.routine _ frame.2 actual

/-- Memory and actual entry context pass through a finite field pipeline.
All normal prefix calls are derived from this same returning execution. -/
theorem pipeline_memory (steps : List Step) (inputName : String) (tail : ProgHOL 64)
    (valid : ∀ step ∈ steps, step.Valid)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p ch cursor zeros query : BitVec 64)
    (context : MerkleMemory.Context source cursor zeros query)
    (pointer : source.locals.lookup (ofString inputName)=some (.val (.word p)))
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (geometry : ∀ step ∈ steps, AllocatedBytes.Arena (p+BitVec.ofNat 64 step.inputOffset) step.length ∧
      AllocatedBytes.Arena (ch+BitVec.ofNat 64 (32*step.field)) 32 ∧
      (ch+BitVec.ofNat 64 (32*step.field)).toNat%8=0 ∧ CopyGeneral.Away (ch+BitVec.ofNat 64 (32*step.field)) query 32)
    (tailFrame : ∀ middle, MerkleMemory.Context middle cursor zeros query →
      evaluateHOLFiniteState source (pipeline inputName steps .skip)=(none,middle) → ∀ value,
      evaluateHOLFiniteState middle tail=(some (.returned value),post) → post.memory query=middle.memory query)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source (pipeline inputName steps tail)=(some (.returned value),post)) :
    post.memory query=source.memory query := by
  induction steps generalizing source with
  | nil => exact tailFrame source context (evaluateHOLFiniteState_skip source) value actual
  | cons step rest ih =>
    change evaluateHOLFiniteState source (.seq (step.program inputName) (pipeline inputName rest tail))=(some (.returned value),post) at actual
    have safe : LocalPrefix (ofString "ch") (step.program inputName) := .call none _ _ (by intro name impossible; cases impossible)
    obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
    have layout := geometry step (by simp)
    have next := step.frame source middle inputName p ch cursor zeros query (valid step (by simp)) context pointer chunks layout.1 layout.2.1 layout.2.2.1 layout.2.2.2 normal
    have kept (name : MlS) := CallNormal.ignored_lookup source middle name step.function (step.arguments inputName) normal
    have suffix := ih (by intro item member; exact valid item (by simp [member])) middle next.2 ((kept _).trans pointer) ((kept _).trans chunks)
      (by intro item member; exact geometry item (by simp [member]))
      (by intro final ready restRun observed tailRun
          apply tailFrame final ready ?_ observed tailRun
          change evaluateHOLFiniteState source (.seq (step.program inputName) (pipeline inputName rest .skip))=(none,final)
          rw [evaluateHOLFiniteState_seq_line780,normal]
          exact restRun) remaining
    exact suffix.trans next.1

end InitECandidate.Solver.Input.CurrentHash.FixedRecord

#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.Step.function_name
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.Step.frame
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.pipeline_memory
