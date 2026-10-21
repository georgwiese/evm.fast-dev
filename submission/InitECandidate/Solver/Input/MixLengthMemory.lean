import InitECandidate.Solver.Input.LittleEndianMemory
import InitECandidate.Solver.Input.MixLengthCallCost
import InitECandidate.Solver.Input.SszHashProtected
import InitECandidate.Solver.Input.ShaPairMemory
import InitECandidate.Solver.Input.CopyZeroMemoryNormal

namespace InitECandidate.Solver.Input.MixLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual original final pair and return preserve words outside the SHA
buffers and actual output. Digest/length values are unrestricted. -/
theorem writer_suffix_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root out chunk stp accel query : BitVec 64) (ready : Ready source root out chunk stp accel)
    (rootArena : AllocatedBytes.Arena root 32) (chunkArena : AllocatedBytes.Arena chunk 32)
    (stateAway : CopyGeneral.Away stp query 64) (accelAway : CopyGeneral.Away accel query 96) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterWriter=(some (.returned value),post)) : post.memory query=source.memory query := by
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "sha256_pair") pairArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,returned⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 run
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) pairArguments=some (ShaPair.values root chunk out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,pairArguments,chunkExpression,localVar,ready.rootLocal,ready.chunk,ready.output,ShaPair.values]
  have pairMemory := ShaPair.call_memory source middle root chunk out stp accel query ready.workspace rootArena chunkArena stateAway accelAway outAway pairArguments args normal
  have tail := MemoryAt.return_current middle (.const 0#64) query
  rw [returned] at tail
  exact tail.trans pairMemory

theorem zero_suffix_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root out chunk stp accel query : BitVec 64) (ready : Ready source root out chunk stp accel)
    (rootArena : AllocatedBytes.Arena root 32) (chunkArena : AllocatedBytes.Arena chunk 32)
    (stateAway : CopyGeneral.Away stp query 64) (accelAway : CopyGeneral.Away accel query 96)
    (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterZero=(some (.returned value),post)) : post.memory query=source.memory query := by
  unfold afterZero at run
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "st_le64") writeArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ afterWriter value (safe.summary_full source).2.1 run
  have written := MemoryWordCalls.le64_call_memory source middle chunkExpression (localVar "len") chunk query ready.workspace.installed
    (by simpa [eval,evalHOLExact,toExact,chunkExpression] using ready.chunk) (by intro offset inside; exact chunkAway offset (by omega)) normal
  have next := Ready.after_call source middle root out chunk stp accel ready (ofString "st_le64") writeArguments (fun key=>
    GlobalEffects.call_body key source.code (some none) (ofString "st_le64") writeArguments MemoryWordCalls.formals MemoryWordCalls.le64Body .one
      (MemoryWordCalls.le64_code source.code ready.workspace.installed) (MemoryWordCalls.le64_globals key source.code ready.workspace.installed)) normal
  exact (writer_suffix_memory middle post root out chunk stp accel query next rootArena chunkArena stateAway accelAway outAway value remaining).trans written

/-- Whole original length mixing preserves a protected decoded word through
zeroing, both little-endian stores, SHA pair and return. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root out chunk stp accel query : BitVec 64) (ready : Ready source root out chunk stp accel)
    (rootArena : AllocatedBytes.Arena root 32) (chunkArena : AllocatedBytes.Arena chunk 32) (aligned : chunk.toNat%8=0)
    (stateAway : CopyGeneral.Away stp query 64) (accelAway : CopyGeneral.Away accel query 96)
    (chunkAway : CopyGeneral.Away chunk query 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [body_shape] at run
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "memzero") zeroArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ afterZero value (safe.summary_full source).2.1 run
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) zeroArguments=some (Zero.values chunk 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,zeroArguments,chunkExpression,ready.chunk,Zero.values]
  have zeroMemory := MemoryAt.zero_normal source middle zeroArguments chunk query 32 args ready.workspace.installed ready.workspace.domain chunkArena aligned (by decide) (fun offset bound=>(chunkAway offset bound).1) normal
  have next := Ready.after_call source middle root out chunk stp accel ready (ofString "memzero") zeroArguments (fun key=>
    GlobalEffects.call_body key source.code (some none) (ofString "memzero") zeroArguments Zero.formals Zero.body .one
      (Zero.original_code source.code ready.workspace.installed) (Zero.globals key source.code)) normal
  exact (zero_suffix_memory middle post root out chunk stp accel query next rootArena chunkArena stateAway accelAway chunkAway outAway value remaining).trans zeroMemory

/-- Real original caller inherits the whole length-mixing frame at its
current initialized workspace and actual three-word ABI. -/
theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root len out chunk zeros stp accel query : BitVec 64)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (rootArena : AllocatedBytes.Arena root 32) (outAway : CopyGeneral.Away out query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values root len out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "mix_in_length") arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨callee,called,rootLocal,outLocal⟩ := environment source.code.lookup root len out (original_code source.code protection.workspace.sha.installed)
  have ready : Ready (callEntryStateHOLFinite source callee) root out chunk stp accel :=
    ⟨rootLocal,outLocal,protection.workspace.chunkLocal,ShaPair.Workspace.at_callee source callee stp accel protection.workspace.sha⟩
  exact MemoryAt.call_normal source post (ofString "mix_in_length") arguments (values root len out) body callee .one query args called
    (fun target value evaluated=>body_memory (callEntryStateHOLFinite source callee) target root out chunk stp accel query ready rootArena protection.workspace.chunkArena
      protection.workspace.chunkAligned protection.stateAway protection.accelAway protection.chunkAway outAway value evaluated) run

end InitECandidate.Solver.Input.MixLength

#print axioms InitECandidate.Solver.Input.MixLength.writer_suffix_memory
#print axioms InitECandidate.Solver.Input.MixLength.zero_suffix_memory
#print axioms InitECandidate.Solver.Input.MixLength.body_memory
#print axioms InitECandidate.Solver.Input.MixLength.call_memory
