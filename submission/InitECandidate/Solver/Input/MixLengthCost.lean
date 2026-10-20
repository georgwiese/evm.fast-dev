import InitECandidate.Solver.Input.MixLengthProgram
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Input.MixLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

theorem writer_suffix_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root out chunk stp accel : BitVec 64)
    (ready : Ready source root out chunk stp accel) (rootArena : AllocatedBytes.Arena root 32) (chunkArena : AllocatedBytes.Arena chunk 32) :
    source.clock-(evaluateHOLFiniteState source afterWriter).2.clock≤53 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) pairArguments=some (ShaPair.values root chunk out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,pairArguments,chunkExpression,QueryBranch.localVar,ready.rootLocal,ready.chunk,ready.output,ShaPair.values]
  have pairCost := ShaPair.call_cost source root chunk out stp accel ready.workspace.installed (some none) pairArguments args
    ready.workspace.state ready.workspace.accelerator ready.workspace.domain rootArena chunkArena ready.workspace.arena ready.workspace.aligned
  exact ClockCost.sequence_current source _ _ 53 0 pairCost (ClockCost.returned source.code _)

theorem zero_suffix_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root out chunk stp accel : BitVec 64)
    (ready : Ready source root out chunk stp accel) (rootArena : AllocatedBytes.Arena root 32) (chunkArena : AllocatedBytes.Arena chunk 32) :
    source.clock-(evaluateHOLFiniteState source afterZero).2.clock≤56 := by
  unfold afterZero
  have writerCost := MemoryWordCalls.le64_call_cost source.code ready.workspace.installed (some none) writeArguments source rfl
  apply ClockCost.sequence_reached_current source _ afterWriter 3 53 writerCost
  intro middle normal
  have next := Ready.after_call source middle root out chunk stp accel ready (ofString "st_le64") writeArguments (fun key=>
    GlobalEffects.call_body key source.code (some none) (ofString "st_le64") writeArguments MemoryWordCalls.formals MemoryWordCalls.le64Body .one
      (MemoryWordCalls.le64_code source.code ready.workspace.installed) (MemoryWordCalls.le64_globals key source.code ready.workspace.installed)) normal
  exact writer_suffix_cost middle root out chunk stp accel next rootArena chunkArena

/-- Whole unchanged mix_in_length costs58body source ticks, including real
zeroing, both le32 writer calls and the SHA pair, on every possible outcome. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root out chunk stp accel : BitVec 64)
    (ready : Ready source root out chunk stp accel) (rootArena : AllocatedBytes.Arena root 32) (chunkArena : AllocatedBytes.Arena chunk 32) (aligned : chunk.toNat%8=0) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤58 := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) zeroArguments=some (Zero.values chunk 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,zeroArguments,chunkExpression,ready.chunk,Zero.values]
  have zeroCost := Zero.call_cost source zeroArguments chunk 32 args (Zero.original_code source.code ready.workspace.installed) (by decide) (by decide) aligned
    (by intro index inside multiple; exact AllocatedBytes.word_mapped source chunk 32 index ready.workspace.domain chunkArena (by omega) aligned multiple)
  change source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memzero") zeroArguments)).2.clock≤2 at zeroCost
  rw [body_shape]
  apply ClockCost.sequence_reached_current source _ afterZero 2 56 zeroCost
  intro middle normal
  have next := Ready.after_call source middle root out chunk stp accel ready (ofString "memzero") zeroArguments (fun key=>
    GlobalEffects.call_body key source.code (some none) (ofString "memzero") zeroArguments Zero.formals Zero.body .one
      (Zero.original_code source.code ready.workspace.installed) (Zero.globals key source.code)) normal
  exact zero_suffix_cost middle root out chunk stp accel next rootArena chunkArena

end InitECandidate.Solver.Input.MixLength

#print axioms InitECandidate.Solver.Input.MixLength.writer_suffix_cost
#print axioms InitECandidate.Solver.Input.MixLength.zero_suffix_cost
#print axioms InitECandidate.Solver.Input.MixLength.body_cost
