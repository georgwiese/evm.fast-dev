import InitECandidate.Solver.Input.CurrentTable.NewContext
import InitECandidate.Solver.Input.NormalHeapEffects

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Current physical workspace and an already reached persistent frontier.
The earlier input boundary is retained separately from later table storage. -/
structure Workspace (source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower : Nat) (stp pad : BitVec 64) : Prop where
  arena : CurrentStartup.ArenaState source
  environment : CurrentKeccak.Hash.Environment source stp pad
  heap : NormalHeapEffects.AtLeast lower source
  lowerDomain : 2701131776≤lower

theorem Workspace.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {lower : Nat} {stp pad : BitVec 64}
    (ready : Workspace source lower stp pad) (same : LocalEffects.erase target=LocalEffects.erase source) : Workspace target lower stp pad := by
  have globals:=congrArg PanSemStateFiniteExact.globals same
  change target.globals=source.globals at globals
  obtain ⟨heap,cell,low,high,aligned⟩:=ready.heap
  exact ⟨ready.arena.of_frame same,ready.environment.of_frame same,⟨heap,by rw [globals]; exact cell,low,high,aligned⟩,ready.lowerDomain⟩

/-- The actual constructor return advances the same reached frontier. -/
theorem New.Returned.workspace {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {heap cap stp pad : BitVec 64} {lower : Nat}
    (returned : New.Returned source post heap cap stp pad) (before : lower≤heap.toNat) (lowerDomain : 2701131776≤lower) :
    Workspace post lower stp pad :=
  ⟨returned.arena,returned.environment,⟨New.endPointer heap cap,returned.heapCell,by have h:=returned.heapAfter; omega,
    returned.geometry.endBound,returned.geometry.endAligned⟩,lowerDomain⟩

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.Workspace.of_frame
#print axioms InitECandidate.Solver.Input.CurrentTable.New.Returned.workspace
