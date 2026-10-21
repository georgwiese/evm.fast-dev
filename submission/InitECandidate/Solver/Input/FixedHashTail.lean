import InitECandidate.Solver.Input.FixedHashPipeline
import InitECandidate.Solver.Input.HeapReleaseReturn

namespace InitECandidate.Solver.Input.FixedHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem count_bounds (kind : Kind) : 2≤kind.count ∧ kind.count≤5 ∧ kind.depth<64 ∧ kind.count≤2^kind.depth := by cases kind <;> decide

theorem count_word (kind : Kind) : (BitVec.ofNat 64 kind.count).toNat=kind.count := by cases kind <;> rfl

def Kind.tailPrice (kind : Kind) := 115*kind.count+55*kind.depth+15

theorem merkle_arguments (kind : Kind) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (ch out : BitVec 64)
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) kind.merkleArguments=
      some (Merkle.values ch (BitVec.ofNat 64 kind.count) (BitVec.ofNat 64 kind.count) out) := by
  simp [Kind.merkleArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,chunks,output,Merkle.values]

theorem after_steps_cost (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p ch out cursor mark stp accel chunk zeros : BitVec 64)
    (ready : Ready source kind.inputName p ch out cursor mark stp accel chunk zeros) (geometry : Geometry p ch cursor kind.length kind.count)
    (outArena : AllocatedBytes.Arena out 32)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source kind.afterSteps=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤kind.tailPrice := by
  have bounds := count_bounds kind
  have buffer : AllocatedBytes.Arena cursor (32*max 1 (2*(BitVec.ofNat 64 kind.count).toNat)) := by
    rw [count_word]
    exact AllocatedBytes.Arena.weaken cursor 1120 _ geometry.arena (by have h:=bounds.2.1; omega)
  have args := merkle_arguments kind source ch out ready.chunks ready.output
  have releaseCost : ClockCost.Bound source.code releaseSuffix 1 := ClockCost.sequence source.code _ _ 1 0
    (HeapScope.release_call_cost source.code ready.workspace.sha.installed (some none) _) (ClockCost.returned source.code _)
  unfold Kind.afterSteps at run
  have price := ClockCost.sequence_terminating source post _ releaseSuffix (115*kind.count+55*kind.depth+14) 1
    (by intro actual target evaluated notTimeout
        have actualPrice := Merkle.call_cost source target ch (BitVec.ofNat 64 kind.count) (BitVec.ofNat 64 kind.count) cursor out zeros stp accel kind.depth bounds.2.2.1
          (by rw [count_word]; exact bounds.2.2.2) (by rw [count_word]; exact bounds.2.2.2) ready.workspace.sha ready.heap ready.workspace.zerosLocal
          (by rw [count_word]; exact geometry.fieldArena) buffer geometry.aligned outArena ready.workspace.zeroArena (some none) kind.merkleArguments args actual evaluated notTimeout
        simpa only [count_word] using actualPrice)
    (by intro middle normal actual target evaluated notTimeout
        have fields := evaluation_fields source middle _ none normal
        have bounded := releaseCost middle fields.2.2.2
        rw [evaluated] at bounded
        exact bounded)
    result run notTimeout
  exact price

theorem after_steps_return_heap (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p ch out cursor mark stp accel chunk zeros : BitVec 64)
    (ready : Ready source kind.inputName p ch out cursor mark stp accel chunk zeros) (geometry : Geometry p ch cursor kind.length kind.count)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source kind.afterSteps=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  have bounds := count_bounds kind
  have buffer : AllocatedBytes.Arena cursor (32*max 1 (2*(BitVec.ofNat 64 kind.count).toNat)) := by
    rw [count_word]
    exact AllocatedBytes.Arena.weaken cursor 1120 _ geometry.arena (by have h:=bounds.2.1; omega)
  have args := merkle_arguments kind source ch out ready.chunks ready.output
  have safe : LocalPrefix (ofString "mark") (.call (some (none,none)) (ofString "merkleize") kind.merkleArguments) := .call none _ _ (by intro name impossible; cases impossible)
  unfold Kind.afterSteps at run
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ releaseSuffix value (safe.summary_full source).2.1 run
  have nextHeap := Merkle.ignored_return_heap source middle ch (BitVec.ofNat 64 kind.count) (BitVec.ofNat 64 kind.count) cursor out stp accel kind.depth bounds.2.2.1
    (by rw [count_word]; exact bounds.2.2.2) (by rw [count_word]; exact bounds.2.2.2) ready.workspace.sha ready.heap
    (by rw [count_word]; exact geometry.fieldArena) buffer geometry.aligned kind.merkleArguments args normal
  have nextMark := (CallNormal.ignored_lookup source middle (ofString "mark") (ofString "merkleize") kind.merkleArguments normal).trans ready.saved
  have fields := evaluation_fields source middle _ none normal
  exact HeapScope.release_return_heap middle post mark cursor (fields.2.2.2.symm ▸ ready.workspace.sha.installed) nextMark nextHeap value remaining

theorem after_steps_globals (kind : Kind) (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code kind.afterSteps :=
  GlobalEffects.sequence key code _ _
    (GlobalEffects.call_body key code (some none) (ofString "merkleize") kind.merkleArguments Merkle.formals Merkle.body .one (Merkle.original_code code installed) (Merkle.globals key code installed different))
    (GlobalEffects.sequence key code _ _
      (GlobalEffects.call_body key code (some none) (ofString "heap_release") [localVar "mark"] HeapScope.releaseFormals HeapScope.releaseBody .one
        (HeapScope.release_original_code code installed) (Merkle.release_globals key code different)) (GlobalEffects.returned key code _))

end InitECandidate.Solver.Input.FixedHash

#print axioms InitECandidate.Solver.Input.FixedHash.count_bounds
#print axioms InitECandidate.Solver.Input.FixedHash.count_word
#print axioms InitECandidate.Solver.Input.FixedHash.merkle_arguments
#print axioms InitECandidate.Solver.Input.FixedHash.after_steps_cost
#print axioms InitECandidate.Solver.Input.FixedHash.after_steps_return_heap
#print axioms InitECandidate.Solver.Input.FixedHash.after_steps_globals
