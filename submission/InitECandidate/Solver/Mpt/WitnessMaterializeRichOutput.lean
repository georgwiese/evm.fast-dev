import InitECandidate.Solver.Mpt.WitnessCoreRichBodyNormal
import InitECandidate.Solver.Mpt.WitnessMaterializeOutput

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessCore WitnessCore.Stack Input.Main.RunAttemptConstructors

/-- The original physical output plus its actual bounded closed node
registry and exact returned membership, independent of callee locals. -/
def RichOutput (input : Guest.InputBlob) (frontier : Nat) (db : BitVec 64)
    (post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64) : Prop :=
  Output input frontier db post returned ∧ ∃ heap child,
    returned=.val (.word child) ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
    ∃ registry : NodeRegistry post frontier heap db,registry.graph.valid child

theorem RichOutput.of_completed (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (completed : RichCompleted input frontier db limit post returned) : RichOutput input frontier db post returned :=
  ⟨Output.of_completed input frontier db limit post returned (completed.to_completed input frontier db limit post returned),
    completed.registry input frontier db limit post returned⟩

theorem RichOutput.of_fields (input : Guest.InputBlob) (frontier : Nat) (db : BitVec 64)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : RichOutput input frontier db source returned)
    (memory : target.memory=source.memory) (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (heap : target.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr"))
    (scratch : ∃ cursor,target.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor))) :
    RichOutput input frontier db target returned := by
  obtain ⟨physical,actualHeap,child,returnedEq,heapCell,registry,member⟩:=output
  obtain ⟨graph,validEq,regions,disjoint,⟨values⟩⟩:=registry.graph.after_agreement source target 1024 frontier actualHeap.toNat (WitnessValue db)
    registry.values registry.regions registry.disjoint domain (fun _ _=>congrFun memory _) (fun _ _=>congrFun memory _)
  refine ⟨physical.of_fields input frontier db source target returned memory domain endian heap scratch,
    actualHeap,child,returnedEq,heap.trans heapCell,⟨graph,values,regions,disjoint⟩,?_⟩
  change graph.valid child
  rw [validEq]
  exact member

theorem RichOutput.of_erase (input : Guest.InputBlob) (frontier : Nat) (db : BitVec 64)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : RichOutput input frontier db source returned) (pure : Input.LocalEffects.erase target=Input.LocalEffects.erase source) :
    RichOutput input frontier db target returned := by
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

theorem RichOutput.release (input : Guest.InputBlob) (frontier : Nat) (db mark : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : RichOutput input frontier db source returned) :
    RichOutput input frontier db (Arenas.Scratch.released {source with clock:=source.clock-1} mark) returned := by
  apply output.of_fields input frontier db source (Arenas.Scratch.released {source with clock:=source.clock-1} mark) returned rfl rfl rfl
  · simp [Arenas.Scratch.released,HolFiniteMapExact.update,FUPDATE,show ofString "scratch_ptr"≠ofString "heap_ptr" from by decide]
  · exact ⟨mark,by simp [Arenas.Scratch.released,HolFiniteMapExact.update,FUPDATE]⟩

end InitECandidate.Solver.Mpt.WitnessMaterialize

#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.RichOutput.of_completed
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.RichOutput.of_fields
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.RichOutput.of_erase
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.RichOutput.release
