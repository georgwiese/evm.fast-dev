import InitECandidate.Solver.Input.MerkleExtensionLoop
import InitECandidate.Solver.Input.ShaPairMemory
import InitECandidate.Solver.Input.MemoryBoundedLoop

namespace InitECandidate.Solver.Input.Merkle
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem extension_step_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor zeros stp accel query : BitVec 64) (index : Nat)
    (small : index<64) (workspace : ShaPair.Workspace source stp accel)
    (bufferArena : AllocatedBytes.Arena cursor 32) (tableArena : AllocatedBytes.Arena zeros 2048)
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (position : source.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 index))))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)))
    (stateAway : CopyGeneral.Away stp query 64) (accelAway : CopyGeneral.Away accel query 96) (bufferAway : CopyGeneral.Away cursor query 32)
    (run : evaluateHOLFiniteState source extensionStep=(none,post)) : post.memory query=source.memory query := by
  rw [extension_shape.2.2.1] at run
  obtain ⟨middle,normal,remaining⟩ := sequence_none source post extensionCall extensionIncrement run
  have zeroArena := AllocatedBytes.Arena.subrange zeros 2048 (32*index) 32 tableArena (by omega)
  have called := ShaPair.call_memory source middle cursor (zeros+BitVec.ofNat 64 (32*index)) cursor stp accel query workspace bufferArena zeroArena stateAway accelAway bufferAway extensionArguments
    (extension_arguments source cursor zeros index buffer position table) normal
  have assigned := MemoryAt.assign_current middle .local (ofString "d") (.op .add [localVar "d",.const 1#64]) query
  change evaluateHOLFiniteState middle (.assign .local (ofString "d") (.op .add [localVar "d",.const 1#64]))=(none,post) at remaining
  rw [remaining] at assigned
  exact assigned.trans called

/-- Actual normal zero-hash extension uses its current bounded depth/table
and preserves words outside the root/state/accelerator write regions. -/
theorem extension_loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor zeros stp accel query : BitVec 64) (index target : Nat)
    (small : target<64) (inside : index≤target) (workspace : ShaPair.Workspace source stp accel)
    (bufferArena : AllocatedBytes.Arena cursor 32) (tableArena : AllocatedBytes.Arena zeros 2048)
    (buffer : source.locals.lookup (ofString "buf")=some (.val (.word cursor)))
    (position : source.locals.lookup (ofString "d")=some (.val (.word (BitVec.ofNat 64 index))))
    (limit : source.locals.lookup (ofString "target")=some (.val (.word (BitVec.ofNat 64 target))))
    (table : source.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)))
    (stateAway : CopyGeneral.Away stp query 64) (accelAway : CopyGeneral.Away accel query 96) (bufferAway : CopyGeneral.Away cursor query 32)
    (run : evaluateHOLFiniteState source extensionLoop=(none,post)) : post.memory query=source.memory query := by
  let invariant := fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>
    current.locals.lookup (ofString "target")=some (.val (.word (BitVec.ofNat 64 target))) ∧ current.locals.lookup (ofString "buf")=some (.val (.word cursor)) ∧
    current.globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)) ∧ ShaPair.Workspace current stp accel
  rw [extension_shape.2.1] at run
  have summary := MemoryAt.bounded_counter_loop_normal source.code (ofString "d") (ofString "buf") extensionTest extensionStep 1 target query
    (extension_other (ofString "buf") (by decide)).summary_full extension_advances invariant
    (by intro current actual; exact ⟨actual.1,actual.2.1,actual.2.2.1,ShaPair.Workspace.of_fields current _ stp accel actual.2.2.2 rfl rfl rfl rfl⟩)
    (by intro current actual position positionBound positionLocal
        have read := extension_test_read current position target small positionBound positionLocal actual.1
        have equivalent : (position<target)=(position+1≤target) := propext (by omega)
        simpa only [equivalent] using read)
    (by intro current codeEq actual position active positionLocal next bodyRun
        have other (name : String) (different : ofString name≠ofString "d") : next.locals.lookup (ofString name)=current.locals.lookup (ofString name) := by
          have localFrame := (extension_other (ofString name) different).summary_full current
          unfold LocalSummary at localFrame
          rw [bodyRun] at localFrame
          exact localFrame.1 rfl
        have tableFrame := extension_globals (ofString "zero_hashes") current.code actual.2.2.2.installed current rfl
        rw [bodyRun] at tableFrame
        have nextTable := (congrArg Prod.snd tableFrame).trans actual.2.2.1
        have nextWorkspace := ShaPair.Workspace.after current next stp accel actual.2.2.2 extensionStep none bodyRun
          (extension_globals (ofString "sha_st") current.code actual.2.2.2.installed) (extension_globals (ofString "sha_accel") current.code actual.2.2.2.installed)
        exact ⟨⟨(other "target" (by decide)).trans actual.1,(other "buf" (by decide)).trans actual.2.1,nextTable,nextWorkspace⟩,
          extension_step_memory current next cursor zeros stp accel query position (by omega) actual.2.2.2 bufferArena tableArena actual.2.1 positionLocal actual.2.2.1 stateAway accelAway bufferAway bodyRun⟩)
    source post index rfl ⟨limit,buffer,table,workspace⟩ inside position run
  exact summary.2.2

end InitECandidate.Solver.Input.Merkle

#print axioms InitECandidate.Solver.Input.Merkle.extension_step_memory
#print axioms InitECandidate.Solver.Input.Merkle.extension_loop_memory
