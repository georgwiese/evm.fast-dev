import InitECandidate.Solver.Input.FixedHashStepMemory
import InitECandidate.Solver.Input.FixedHashCall
import InitECandidate.Solver.Input.HeapReleaseMemory

namespace InitECandidate.Solver.Input.FixedHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Original dense tree/output/release tail preserves a protected word. -/
theorem after_steps_memory (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p ch out cursor mark stp accel chunk zeros query : BitVec 64)
    (ready : Ready source kind.inputName p ch out cursor mark stp accel chunk zeros)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (geometry : Geometry p ch cursor kind.length kind.count) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<cursor.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source kind.afterSteps=(some (.returned value),post)) : post.memory query=source.memory query := by
  have bounds := count_bounds kind
  have buffer : AllocatedBytes.Arena cursor (32*max 1 (2*(BitVec.ofNat 64 kind.count).toNat)) := by
    rw [count_word]
    exact AllocatedBytes.Arena.weaken cursor 1120 _ geometry.arena (by have h:=bounds.2.1; omega)
  have args := merkle_arguments kind source ch out ready.chunks ready.output
  have safe : LocalPrefix (ofString "mark") (.call (some (none,none)) (ofString "merkleize") kind.merkleArguments) := .call none _ _ (by intro name impossible; cases impossible)
  unfold Kind.afterSteps at run
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ releaseSuffix value (safe.summary_full source).2.1 run
  have front := Merkle.call_memory source middle ch (BitVec.ofNat 64 kind.count) (BitVec.ofNat 64 kind.count) cursor out stp accel chunk zeros query kind.depth bounds.2.2.1
    (by rw [count_word]; exact bounds.2.2.2) (by rw [count_word]; exact bounds.2.2.2) protection ready.heap
    (by rw [count_word]; exact geometry.fieldArena) buffer geometry.aligned outArena below outAway kind.merkleArguments args normal
  have fields := evaluation_fields source middle _ none normal
  have tail := HeapScope.release_return_memory middle post [localVar "mark"] query (fields.2.2.2.symm ▸ ready.workspace.sha.installed) value remaining
  exact tail.trans front

/-- Real fixed record allocation and field pipeline preserve a protected
word below their entry cursor and outside the actual caller output. -/
theorem after_mark_memory (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p ch out mark stp accel chunk zeros query : BitVec 64)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (pointer : source.locals.lookup (ofString kind.inputName)=some (.val (.word p)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (inputArena : AllocatedBytes.Arena p kind.length) (arena : AllocatedBytes.Arena ch (32*kind.count+1120))
    (aligned : ch.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<ch.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source kind.afterMark=(some (.returned value),post)) : post.memory query=source.memory query := by
  obtain ⟨paid,final,remaining,endpoint⟩ := allocation_trace kind source post ch protection.workspace.sha.installed heap arena (some (.returned value)) run (by simp)
  obtain ⟨round,geometry⟩ := allocation_geometry kind ch p inputArena arena aligned
  let entry := kind.allocated source ch
  have ready := allocated_ready kind source p ch out mark stp accel chunk zeros protection.workspace pointer output saved round
  have entryProtection := protection.with_workspace source entry stp accel chunk zeros query ready.workspace
  have number : (kind.cursor ch).toNat=ch.toNat+32*kind.count := byteAddress_toNat ch (32*kind.count) (by have h:=arena.upper; omega)
  have tempBelow : query.toNat<(kind.cursor ch).toNat := by rw [number]; omega
  have fieldsAway := CopyGeneral.Away.after ch query (32*kind.count) aligned (by have h:=arena.upper; omega) below
  have frame := pipeline_memory kind.steps kind.inputName kind.afterSteps kind.length kind.count p ch out (kind.cursor ch) mark stp accel chunk zeros query
    (steps_valid kind) geometry tempBelow fieldsAway
    (fun current target currentReady currentProtection value evaluated=>after_steps_memory kind current target p ch out (kind.cursor ch) mark stp accel chunk zeros query
      currentReady currentProtection geometry outArena tempBelow outAway value evaluated)
    entry final ready entryProtection value remaining
  rw [endpoint]
  exact frame

/-- Whole unchanged fixed record hashes preserve arbitrary decoded words
through all actual field hashes, both allocation scopes and the final tree. -/
theorem body_memory (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p ch out stp accel chunk zeros query : BitVec 64)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (pointer : source.locals.lookup (ofString kind.inputName)=some (.val (.word p)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (inputArena : AllocatedBytes.Arena p kind.length) (arena : AllocatedBytes.Arena ch (32*kind.count+1120))
    (aligned : ch.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<ch.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source kind.body=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [body_shape] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post ch "mark" kind.afterMark heap
    (HeapScope.mark_original_code source.code protection.workspace.sha.installed) (some (.returned value)) run (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" ch
  have nextProtection := SszHash.Protected.of_fields source entry stp accel chunk zeros query protection rfl rfl (by intro key different; rfl)
  have other (name : String) (different : ofString "mark"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) := bind_lookup_other _ "mark" name ch different
  have frame := after_mark_memory kind entry final p ch out ch stp accel chunk zeros query nextProtection
    ((other kind.inputName (by cases kind <;> decide)).trans pointer) ((other "out" (by decide)).trans output) (bind_lookup_same _ _ _)
    heap inputArena arena aligned outArena below outAway value remaining
  rw [endpoint]
  exact frame

/-- All six real fixed-record caller ABIs inherit their whole memory frame. -/
theorem call_memory (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (p ch out stp accel chunk zeros query : BitVec 64)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (inputArena : AllocatedBytes.Arena p kind.length) (arena : AllocatedBytes.Arena ch (32*kind.count+1120))
    (aligned : ch.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<ch.toNat) (outAway : CopyGeneral.Away out query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) kind.name arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨callee,called,pLocal,outLocal⟩ := environment kind source.code.lookup p out (original_code kind source.code protection.workspace.sha.installed)
  exact MemoryAt.call_normal source post kind.name arguments (values p out) kind.body callee .one query args called
    (fun target value evaluated=>body_memory kind (callEntryStateHOLFinite source callee) target p ch out stp accel chunk zeros query
      (SszHash.Protected.at_callee source callee stp accel chunk zeros query protection) pLocal outLocal heap inputArena arena aligned outArena below outAway value evaluated) run

end InitECandidate.Solver.Input.FixedHash

#print axioms InitECandidate.Solver.Input.FixedHash.after_steps_memory
#print axioms InitECandidate.Solver.Input.FixedHash.after_mark_memory
#print axioms InitECandidate.Solver.Input.FixedHash.body_memory
#print axioms InitECandidate.Solver.Input.FixedHash.call_memory
