import InitECandidate.Solver.Input.MerkleInnerLoop
import InitECandidate.Solver.Input.ShaPairMemory
import InitECandidate.Solver.Input.MemoryBoundedLoop

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem inner_step_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor stp accel query : BitVec 64) (index half : Nat)
    (workspace : ShaPair.Workspace source stp accel) (active : index<half) (arena : AllocatedBytes.Arena cursor (64*half))
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (position : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 index))))
    (stateAway : CopyGeneral.Away stp query 64) (accelAway : CopyGeneral.Away accel query 96) (bufferAway : CopyGeneral.Away cursor query (64*half))
    (run : evaluateHOLFiniteState source innerStep=(none,post)) : post.memory query=source.memory query := by
  rw [inner_shape.2] at run
  obtain ⟨middle,normal,remaining⟩ := sequence_none source post innerCall innerIncrement run
  have aArena := AllocatedBytes.Arena.subrange cursor (64*half) (64*index) 32 arena (by omega)
  have bArena := AllocatedBytes.Arena.subrange cursor (64*half) (64*index+32) 32 arena (by omega)
  have outAway := CopyGeneral.Away.subrange cursor query (64*half) (32*index) 32 bufferAway (by omega)
  have called := ShaPair.call_memory source middle _ _ _ stp accel query workspace aArena bArena stateAway accelAway outAway innerArguments (inner_arguments source cursor index buffer position) normal
  have assigned := MemoryAt.assign_current middle .local (ofString "j") (.op .add [localVar "j",.const 1#64]) query
  change evaluateHOLFiniteState middle (.assign .local (ofString "j") (.op .add [localVar "j",.const 1#64]))=(none,post) at remaining
  rw [remaining] at assigned
  exact assigned.trans called

/-- Real dense pair-loop memory frame, at each actual j<half. Current
workspace and buffer/limit bindings are derived through normal iterations. -/
theorem inner_loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor stp accel query : BitVec 64) (index half : Nat)
    (small : half<2^63) (inside : index≤half) (workspace : ShaPair.Workspace source stp accel) (arena : AllocatedBytes.Arena cursor (64*half))
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (position : source.locals.lookup (ofString "j")=some (.val (.word (BitVec.ofNat 64 index))))
    (limit : source.locals.lookup (ofString "half")=some (.val (.word (BitVec.ofNat 64 half))))
    (stateAway : CopyGeneral.Away stp query 64) (accelAway : CopyGeneral.Away accel query 96) (bufferAway : CopyGeneral.Away cursor query (64*half))
    (run : evaluateHOLFiniteState source innerLoop=(none,post)) : post.memory query=source.memory query := by
  let invariant := fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>
    current.locals.lookup (ofString "half")=some (.val (.word (BitVec.ofNat 64 half))) ∧ current.locals.lookup (ofString "buf")=some (.val (.word cursor)) ∧ ShaPair.Workspace current stp accel
  rw [inner_shape.1] at run
  have summary := MemoryAt.bounded_counter_loop_normal source.code (ofString "j") (ofString "buf") innerTest innerStep 1 half query
    (inner_other (ofString "buf") (by decide)).summary_full inner_advances invariant
    (by intro current actual; exact ⟨actual.1,actual.2.1,ShaPair.Workspace.of_fields current _ stp accel actual.2.2 rfl rfl rfl rfl⟩)
    (by intro current actual position positionBound positionLocal
        have read := inner_test_read current position half small positionBound positionLocal actual.1
        have equivalent : (position<half)=(position+1≤half) := propext (by omega)
        simpa only [equivalent] using read)
    (by intro current codeEq actual position active positionLocal target bodyRun
        have other (name : String) (different : ofString name≠ofString "j") : target.locals.lookup (ofString name)=current.locals.lookup (ofString name) := by
          have localFrame := (inner_other (ofString name) different).summary_full current
          unfold LocalSummary at localFrame
          rw [bodyRun] at localFrame
          exact localFrame.1 rfl
        have nextWorkspace := ShaPair.Workspace.after current target stp accel actual.2.2 innerStep none bodyRun
          (inner_globals (ofString "sha_st") current.code actual.2.2.installed) (inner_globals (ofString "sha_accel") current.code actual.2.2.installed)
        exact ⟨⟨(other "half" (by decide)).trans actual.1,(other "buf" (by decide)).trans actual.2.1,nextWorkspace⟩,
          inner_step_memory current target cursor stp accel query position half actual.2.2 (by omega) arena actual.2.1 positionLocal stateAway accelAway bufferAway bodyRun⟩)
    source post index rfl ⟨limit,buffer,workspace⟩ inside position run
  exact summary.2.2

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.inner_step_memory
#print axioms InitECandidate.Solver.Input.Merkle.inner_loop_memory
