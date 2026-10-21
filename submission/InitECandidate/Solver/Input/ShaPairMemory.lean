import InitECandidate.Solver.Input.ShaPairStageMemory
import InitECandidate.Solver.Input.ShaWorkspace

namespace InitECandidate.Solver.Input.ShaPair
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem Stage.summary (stage : Stage) (key : MlS) (source : PanSemStateFiniteExact 64 Guest.HostMemory) : LocalSummary key stage.program source := by
  cases stage <;> simp only [Stage.program]
  all_goals first
    | exact (LocalPrefix.call none _ _ (by intro name impossible; cases impossible)).summary_full source
    | exact byte_store_local key _ _ source

theorem program_memory (phases : List Stage) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (a b out stp accel query : BitVec 64)
    (ready : MemoryReady source a b out stp accel)
    (aArena : AllocatedBytes.Arena a 32) (bArena : AllocatedBytes.Arena b 32) (arena : AllocatedBytes.Arena accel 96) (aligned : accel.toNat%8=0)
    (stateAway : CopyGeneral.Away stp query 64) (accelAway : CopyGeneral.Away accel query 96) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (program phases)=(some (.returned value),post)) : post.memory query=source.memory query := by
  induction phases generalizing source post with
  | nil=>
    have frame := MemoryAt.return_current source (.const 0#64) query
    change evaluateHOLFiniteState source (.return (.const 0#64))=(some (.returned value),post) at run
    rw [run] at frame
    exact frame
  | cons phase rest ih=>
    obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post phase.program (program rest) value (phase.summary (ofString "out") source).2.1 run
    have front := phase.memory source middle a b out stp accel query ready aArena bArena arena aligned stateAway accelAway outAway normal
    have next := MemoryReady.after phase source middle a b out stp accel ready normal
    exact (ih middle post next remaining).trans front

/-- Complete unchanged sha256_pair memory frame, including initialization,
two mapped input copies, both actual in-place blocks, padding/length and
normal finish. Arbitrary SHA/FFI output values remain unrestricted. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (a b out stp accel query : BitVec 64)
    (ready : MemoryReady source a b out stp accel)
    (aArena : AllocatedBytes.Arena a 32) (bArena : AllocatedBytes.Arena b 32) (arena : AllocatedBytes.Arena accel 96) (aligned : accel.toNat%8=0)
    (stateAway : CopyGeneral.Away stp query 64) (accelAway : CopyGeneral.Away accel query 96) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source ShaFixedCost.pairBody=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [original_shape] at run
  exact program_memory stages source post a b out stp accel query ready aArena bArena arena aligned stateAway accelAway outAway value run

theorem memory_environment (codeFn : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) (a b out : BitVec 64)
    (code : codeFn (ofString "sha256_pair")=some (ShaFixedCost.pairFormals,ShaFixedCost.pairBody,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),lookupCodeHOLFinite codeFn (ofString "sha256_pair") (values a b out)=some (ShaFixedCost.pairBody,callee,.one) ∧
      callee.lookup (ofString "input_a")=some (.val (.word a)) ∧ callee.lookup (ofString "input_b")=some (.val (.word b)) ∧ callee.lookup (ofString "out")=some (.val (.word out)) := by
  have valid : (ShaFixedCost.pairFormals.map Prod.fst).Nodup ∧ ShaFixedCost.pairFormals.length=(values a b out).length ∧
      ((ShaFixedCost.pairFormals.zip (values a b out)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true := by
    refine ⟨by decide,rfl,?_⟩
    simp [ShaFixedCost.pairFormals,values,shapeEqHOL,shapeOfHOLExact]
  have raw : lookupCodeHOLExact codeFn (ofString "sha256_pair") (values a b out)=some (ShaFixedCost.pairBody,rawLocals a b out,.one) := by
    simp only [lookupCodeHOLExact,code,valid]
    rfl
  obtain ⟨callee,called,locals⟩ := CodeEnvironment.finite_lookup codeFn _ _ _ _ _ raw
  exact ⟨callee,called,by rw [locals]; simp [rawLocals,show ofString "input_a"≠ofString "out" from by decide,show ofString "input_a"≠ofString "input_b" from by decide],
    by rw [locals]; simp [rawLocals,show ofString "input_b"≠ofString "out" from by decide],by rw [locals]; simp [rawLocals]⟩

/-- The real normal pair caller preserves protected input/decoded words
outside the actual SHA buffers and actual output. All callee facts come
from that same caller; no collision or cryptographic assumption is used. -/
theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (a b out stp accel query : BitVec 64)
    (workspace : Workspace source stp accel)
    (aArena : AllocatedBytes.Arena a 32) (bArena : AllocatedBytes.Arena b 32)
    (stateAway : CopyGeneral.Away stp query 64) (accelAway : CopyGeneral.Away accel query 96) (outAway : CopyGeneral.Away out query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values a b out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "sha256_pair") arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨callee,called,inputA,inputB,output⟩ := memory_environment source.code.lookup a b out (ShaFixedCost.pair_code source.code workspace.installed)
  have ready : MemoryReady (callEntryStateHOLFinite source callee) a b out stp accel :=
    ⟨⟨workspace.installed,workspace.domain,inputA,inputB,workspace.state,workspace.accelerator⟩,output⟩
  exact MemoryAt.call_normal source post (ofString "sha256_pair") arguments (values a b out) ShaFixedCost.pairBody callee .one query args called
    (fun target value evaluated=>body_memory (callEntryStateHOLFinite source callee) target a b out stp accel query ready aArena bArena workspace.arena workspace.aligned stateAway accelAway outAway value evaluated) run

end InitECandidate.Solver.Input.ShaPair

#print axioms InitECandidate.Solver.Input.ShaPair.Stage.summary
#print axioms InitECandidate.Solver.Input.ShaPair.program_memory
#print axioms InitECandidate.Solver.Input.ShaPair.body_memory
#print axioms InitECandidate.Solver.Input.ShaPair.memory_environment
#print axioms InitECandidate.Solver.Input.ShaPair.call_memory
