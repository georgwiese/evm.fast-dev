import InitECandidate.Solver.Mpt.WitnessCorePathBodyNormal
import InitECandidate.Solver.Mpt.WitnessMaterializeRichOutput
import InitECandidate.Solver.Mpt.WitnessMaterializeOutput

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessCore WitnessCore.Stack Input.Main.RunAttemptConstructors

/-- The original physical output plus its actual bounded closed node
registry and exact returned membership, independent of callee locals. -/
def PathOutput (input : Guest.InputBlob) (frontier : Nat) (db : BitVec 64)
    (post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64) : Prop :=
  Output input frontier db post returned ∧ ∃ heap child,
    returned=.val (.word child) ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
    ∃ registry : NodeRegistry post frontier heap db,registry.PathModel ∧ registry.graph.valid child

theorem PathOutput.of_completed (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (completed : PathCompleted input frontier db limit post returned) : PathOutput input frontier db post returned :=
  ⟨Output.of_completed input frontier db limit post returned (completed.to_completed input frontier db limit post returned),
    completed.registry input frontier db limit post returned⟩

theorem PathOutput.of_fields (input : Guest.InputBlob) (frontier : Nat) (db : BitVec 64)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : PathOutput input frontier db source returned)
    (memory : target.memory=source.memory) (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (heap : target.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr"))
    (scratch : ∃ cursor,target.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor))) :
    PathOutput input frontier db target returned := by
  obtain ⟨physical,actualHeap,child,returnedEq,heapCell,registry,paths,member⟩:=output
  obtain ⟨graph,validEq,regions,disjoint,⟨values⟩⟩:=registry.graph.after_agreement source target 1024 frontier actualHeap.toNat (WitnessValue db)
    registry.values registry.regions registry.disjoint domain (fun _ _=>congrFun memory _) (fun _ _=>congrFun memory _)
  let next : NodeRegistry target frontier actualHeap db:=⟨graph,values,regions,disjoint⟩
  have agree : ∀ query,registry.graph.Footprint query → target.memory query=source.memory query:=by intros; rw [memory]
  have nextPaths : next.PathModel:=
    ⟨paths.bytes.of_agreement source.memory target.memory source.memaddrs target.memaddrs source.be target.be registry.graph graph validEq domain endian agree (by intros; rw [memory]),
      paths.regions.of_agreement source.memory target.memory source.memaddrs target.memaddrs registry.graph graph frontier actualHeap.toNat validEq agree,
      paths.separated.of_agreement source.memory target.memory source.memaddrs target.memaddrs registry.graph graph validEq agree⟩
  refine ⟨physical.of_fields input frontier db source target returned memory domain endian heap scratch,
    actualHeap,child,returnedEq,heap.trans heapCell,next,nextPaths,?_⟩
  change graph.valid child
  rw [validEq]
  exact member

theorem PathOutput.of_erase (input : Guest.InputBlob) (frontier : Nat) (db : BitVec 64)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : PathOutput input frontier db source returned) (pure : Input.LocalEffects.erase target=Input.LocalEffects.erase source) :
    PathOutput input frontier db target returned := by
  have domain:=congrArg PanSemStateFiniteExact.memaddrs pure
  change target.memaddrs=source.memaddrs at domain
  have endian:=congrArg PanSemStateFiniteExact.be pure
  change target.be=source.be at endian
  have globals:=congrArg PanSemStateFiniteExact.globals pure
  change target.globals=source.globals at globals
  have saved:=output.1
  obtain ⟨actualHeap,child,returnedEq,heapCell,arena,aligned,grows,scratch,frozen,owned⟩:=saved
  obtain ⟨cursor,cursorCell⟩:=scratch
  exact output.of_fields input frontier db source target returned (Input.LocalEffects.memory_of_erase source target pure) domain endian (by rw [globals])
    ⟨cursor,by rw [globals]; exact cursorCell⟩

theorem PathOutput.release (input : Guest.InputBlob) (frontier : Nat) (db mark : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : PathOutput input frontier db source returned) :
    PathOutput input frontier db (Arenas.Scratch.released {source with clock:=source.clock-1} mark) returned := by
  apply output.of_fields input frontier db source (Arenas.Scratch.released {source with clock:=source.clock-1} mark) returned rfl rfl rfl
  · simp [Arenas.Scratch.released,HolFiniteMapExact.update,FUPDATE,show ofString "scratch_ptr"≠ofString "heap_ptr" from by decide]
  · exact ⟨mark,by simp [Arenas.Scratch.released,HolFiniteMapExact.update,FUPDATE]⟩

theorem PathOutput.to_rich_output (input : Guest.InputBlob) (frontier : Nat) (db : BitVec 64)
    (post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : PathOutput input frontier db post returned) : RichOutput input frontier db post returned := by
  obtain ⟨physical,heap,child,returnedEq,heapCell,registry,paths,member⟩:=output
  exact ⟨physical,heap,child,returnedEq,heapCell,registry,member⟩

end InitECandidate.Solver.Mpt.WitnessMaterialize

#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.PathOutput.of_completed
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.PathOutput.of_fields
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.PathOutput.of_erase
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.PathOutput.release

#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.PathOutput.to_rich_output
