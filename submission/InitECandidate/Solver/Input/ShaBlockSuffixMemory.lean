import InitECandidate.Solver.Input.ShaBlockLoopMemory
import InitECandidate.Solver.Input.ForeignMemoryAway
import InitECandidate.Solver.Input.ExternalLocal
import InitECandidate.Solver.Input.AssignNormal

namespace InitECandidate.Solver.Input.ShaFixedCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem second_suffix_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer accel query : BitVec 64)
    (ready : BlockMemoryReady source pointer accel) (position : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (stateAway : CopyGeneral.Away pointer query 64) (accelAway : CopyGeneral.Away accel query 96)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source secondSuffix=(some (.returned value),post)) : post.memory query=source.memory query := by
  have safe : LocalPrefix (ofString "stp") (.while (.cmp .less (localVar "i") (.const 4#64)) secondStep) :=
    .loop _ (LoopPhase.unpack.other (ofString "stp") (by decide) (by decide) (by decide) (by decide))
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ (.return (.const 0#64)) value (safe.summary_full source).2.1 run
  have summary := LoopPhase.memory .unpack source middle pointer accel query ready position stateAway accelAway normal
  have finalFrame := MemoryAt.return_current middle (.const 0#64) query
  rw [remaining] at finalFrame
  exact finalFrame.trans summary.2.2

theorem reset_suffix_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer accel query : BitVec 64)
    (ready : BlockMemoryReady source pointer accel)
    (stateAway : CopyGeneral.Away pointer query 64) (accelAway : CopyGeneral.Away accel query 96)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (.seq resetCounter secondSuffix)=(some (.returned value),post)) : post.memory query=source.memory query := by
  have safe : LocalPrefix (ofString "stp") resetCounter := .assign _ _ (by decide)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post resetCounter secondSuffix value (safe.summary_full source).2.1 run
  have middleEq := assign_none source middle "i" (.const 0#64) 0#64 rfl normal
  have nextReady : BlockMemoryReady middle pointer accel := by
    rw [middleEq]
    exact ⟨(bind_lookup_other source "i" "stp" 0#64 (by decide)).trans ready.state,ready.accelerator⟩
  have position : middle.locals.lookup (ofString "i")=some (.val (.word 0#64)) := by rw [middleEq]; exact bind_lookup_same _ _ _
  have frame := second_suffix_memory middle post pointer accel query nextReady position stateAway accelAway value remaining
  rw [middleEq] at frame
  exact frame

theorem accelerator_suffix_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer accel query : BitVec 64)
    (ready : BlockMemoryReady source pointer accel)
    (stateAway : CopyGeneral.Away pointer query 64) (accelAway : CopyGeneral.Away accel query 96)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (.seq accelerator (.seq resetCounter secondSuffix))=(some (.returned value),post)) : post.memory query=source.memory query := by
  have safe : LocalSummary (ofString "stp") accelerator source := external_local (ofString "stp") _ _ _ _ _ source
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post accelerator _ value safe.2.1 run
  have localFrame := safe
  unfold LocalSummary at localFrame
  rw [normal] at localFrame
  have globalFrame := GlobalEffects.external (ofString "sha_accel") source.code (ofString "sha256f") (.var .global (ofString "sha_accel")) (.const 0#64) (.var .global (ofString "sha_accel")) (.const 96#64) source rfl
  change GlobalEffects.erase (ofString "sha_accel") (evaluateHOLFiniteState source accelerator).2=_ at globalFrame
  rw [normal] at globalFrame
  have nextReady : BlockMemoryReady middle pointer accel := ⟨(localFrame.1 rfl).trans ready.state,(congrArg Prod.snd globalFrame).trans ready.accelerator⟩
  have read : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (.var .global (ofString "sha_accel"))=some (.val (.word accel)) := by
    simp [evalHOLFinite,evalHOLExact,toExact,ready.accelerator]
  have foreignFrame := MemoryAt.foreign_current source (ofString "sha256f") (.var .global (ofString "sha_accel")) (.var .global (ofString "sha_accel")) accel accel query 96 (by decide) read read
    (by intro offset inside; exact (accelAway offset inside).2)
  change (evaluateHOLFiniteState source accelerator).2.memory query=source.memory query at foreignFrame
  rw [normal] at foreignFrame
  exact (reset_suffix_memory middle post pointer accel query nextReady stateAway accelAway value remaining).trans foreignFrame

/-- Exact original pack/FFI/reset/unpack suffix preserves every word
outside the real state64 and accelerator96 regions, at any actual normal
return and with arbitrary cryptographic results. -/
theorem block_suffix_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer accel query : BitVec 64)
    (ready : BlockMemoryReady source pointer accel)
    (stateAway : CopyGeneral.Away pointer query 64) (accelAway : CopyGeneral.Away accel query 96)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source blockSuffix=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [block_suffix_shape] at run
  refine MemoryAt.declaration_returned source post "i" (.const 0#64) 0#64 query _ value rfl ?_ run
  intro inner remaining
  let entry := bind source "i" 0#64
  have nextReady : BlockMemoryReady entry pointer accel := ⟨(bind_lookup_other source "i" "stp" 0#64 (by decide)).trans ready.state,ready.accelerator⟩
  have safe : LocalPrefix (ofString "stp") (.while (.cmp .less (localVar "i") (.const 4#64)) firstStep) :=
    .loop _ (LoopPhase.pack.other (ofString "stp") (by decide) (by decide) (by decide) (by decide))
  obtain ⟨middle,normal,afterLoop⟩ := Input.sequence_returned entry inner _ (.seq accelerator (.seq resetCounter secondSuffix)) value (safe.summary_full entry).2.1 remaining
  have summary := LoopPhase.memory .pack entry middle pointer accel query nextReady (bind_lookup_same _ _ _) stateAway accelAway normal
  have rest := accelerator_suffix_memory middle inner pointer accel query summary.1 stateAway accelAway value afterLoop
  exact rest.trans summary.2.2

end InitECandidate.Solver.Input.ShaFixedCost

#print axioms InitECandidate.Solver.Input.ShaFixedCost.second_suffix_memory
#print axioms InitECandidate.Solver.Input.ShaFixedCost.reset_suffix_memory
#print axioms InitECandidate.Solver.Input.ShaFixedCost.accelerator_suffix_memory
#print axioms InitECandidate.Solver.Input.ShaFixedCost.block_suffix_memory
