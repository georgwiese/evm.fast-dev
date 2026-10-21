import InitECandidate.Solver.Input.FixedHashPipeline
import InitECandidate.Solver.Input.BytesVectorMemory
import InitECandidate.Solver.Input.U64HashMemory

namespace InitECandidate.Solver.Input.FixedHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Every actual normal original scalar/vector/copy field step preserves a
protected decoded word outside its field array and below temporary storage. -/
theorem Step.memory (step : Step) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (inputName : String) (p ch cursor stp accel chunk zeros query : BitVec 64)
    (inputLength fields : Nat) (valid : step.Valid inputLength fields)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (pointer : source.locals.lookup (ofString inputName)=some (.val (.word p)))
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (geometry : Geometry p ch cursor inputLength fields)
    (below : query.toNat<cursor.toNat) (fieldsAway : CopyGeneral.Away ch query (32*fields))
    (run : evaluateHOLFiniteState source (step.program inputName)=(none,post)) : post.memory query=source.memory query := by
  have inputSlice := AllocatedBytes.Arena.subrange p inputLength step.inputOffset step.length geometry.inputArena valid.1
  have outputSlice := AllocatedBytes.Arena.subrange ch (32*fields) (32*step.field) 32 geometry.fieldArena (by have h:=valid.2.1; omega)
  have outputNumber : (ch+BitVec.ofNat 64 (32*step.field)).toNat=ch.toNat+32*step.field := byteAddress_toNat ch (32*step.field) (by have h:=geometry.fieldArena.upper; have f:=valid.2.1; omega)
  have outputAligned : (ch+BitVec.ofNat 64 (32*step.field)).toNat%8=0 := by rw [outputNumber]; have h:=geometry.fieldAligned; omega
  have outputAway := CopyGeneral.Away.subrange ch query (32*fields) (32*step.field) 32 fieldsAway (by have h:=valid.2.1; omega)
  have args := step.arguments_read source inputName p ch pointer chunks
  cases step with
  | scalar offset field=>
    exact U64Hash.call_memory source post (p+BitVec.ofNat 64 offset) (ch+BitVec.ofNat 64 (32*field)) query
      protection.workspace.sha.installed protection.workspace.sha.domain inputSlice outputSlice outputAligned outputAway _ args run
  | copy offset field=>
    exact MemoryAt.copy_normal source post _ (p+BitVec.ofNat 64 offset) (ch+BitVec.ofNat 64 (32*field)) query 32 args
      protection.workspace.sha.installed protection.workspace.sha.domain inputSlice outputSlice outputAway run
  | vector offset length field depth=>
    have constraints := valid.2.2
    have temporary := AllocatedBytes.Arena.weaken cursor 1120 (832+96*PackBytes.chunks length) geometry.arena constraints.2.2.2
    exact BytesVector.call_memory source post (p+BitVec.ofNat 64 offset) cursor (ch+BitVec.ofNat 64 (32*field)) stp accel chunk zeros query length depth
      constraints.1 constraints.2.1 constraints.2.2.1 protection heap inputSlice temporary geometry.aligned outputSlice outputAligned below outputAway _ args run

/-- Compose the original finite field pipeline with the same observed
normal transitions that establish its next workspace and heap bindings. -/
theorem pipeline_memory (steps : List Step) (inputName : String) (tail : ProgHOL 64) (inputLength fields : Nat)
    (p ch out cursor mark stp accel chunk zeros query : BitVec 64)
    (valid : ∀ step∈steps,step.Valid inputLength fields) (geometry : Geometry p ch cursor inputLength fields)
    (below : query.toNat<cursor.toNat) (fieldsAway : CopyGeneral.Away ch query (32*fields))
    (tailFrame : ∀ source post : PanSemStateFiniteExact 64 Guest.HostMemory,
      Ready source inputName p ch out cursor mark stp accel chunk zeros → SszHash.Protected source stp accel chunk zeros query → ∀ value,
      evaluateHOLFiniteState source tail=(some (.returned value),post) → post.memory query=source.memory query)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ready : Ready source inputName p ch out cursor mark stp accel chunk zeros)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (pipeline inputName steps tail)=(some (.returned value),post)) : post.memory query=source.memory query := by
  induction steps generalizing source post with
  | nil=>exact tailFrame source post ready protection value run
  | cons step rest ih=>
    have stepValid := valid step (by simp)
    change evaluateHOLFiniteState source (.seq (step.program inputName) (pipeline inputName rest tail))=(some (.returned value),post) at run
    have safe : LocalPrefix (ofString "mark") (step.program inputName) := .call none _ _ (by intro name impossible; cases impossible)
    obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ _ value (safe.summary_full source).2.1 run
    have front := step.memory source middle inputName p ch cursor stp accel chunk zeros query inputLength fields stepValid protection ready.pointer ready.chunks ready.heap geometry below fieldsAway normal
    have next := step.after source middle inputName p ch out cursor mark stp accel chunk zeros inputLength fields stepValid ready geometry normal
    have nextProtection := protection.with_workspace source middle stp accel chunk zeros query next.workspace
    exact (ih (by intro next member; exact valid next (by simp [member])) middle post next nextProtection remaining).trans front

end InitECandidate.Solver.Input.FixedHash

#print axioms InitECandidate.Solver.Input.FixedHash.Step.memory
#print axioms InitECandidate.Solver.Input.FixedHash.pipeline_memory
