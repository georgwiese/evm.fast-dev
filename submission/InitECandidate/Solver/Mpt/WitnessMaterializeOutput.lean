import InitECandidate.Solver.Mpt.WitnessCoreBodyNormal
import InitECandidate.Solver.Arenas.ScratchScope

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessCore WitnessCore.Stack Input.Main.RunAttemptConstructors

/-- Physical current materializer output, independent of cleared callee
locals. It retains the real bounded heap, built Patricia database and owned
result while the wrappers may restore the scratch cursor. -/
def Output (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db : BitVec 64)
    (post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64) : Prop:=
  ∃ heap child,returned=.val (.word child) ∧
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
    AllocatedBytes.Arena heap 0 ∧ heap.toNat≤2952790016 ∧ heap.toNat%8=0 ∧ frontier≤heap.toNat ∧
    (∃ cursor,post.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor))) ∧
    (Input.CurrentTable.New.endPointer databaseData.table databaseData.cap).toNat≤frontier ∧
    Input.CurrentTable.NodeLookup.Database post databaseData ∧ ResultOwned post frontier heap.toNat child

theorem Output.of_completed (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db limit : BitVec 64)
    (post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (completed : Completed databaseData frontier db limit post returned) : Output databaseData frontier db post returned := by
  obtain ⟨heap,cursor,child,finished,returnedEq,invariant,pure,owned⟩:=completed
  have memory:=Input.LocalEffects.memory_of_erase finished post pure
  have domain:=congrArg PanSemStateFiniteExact.memaddrs pure
  change post.memaddrs=finished.memaddrs at domain
  have endian:=congrArg PanSemStateFiniteExact.be pure
  change post.be=finished.be at endian
  have globals:=congrArg PanSemStateFiniteExact.globals pure
  change post.globals=finished.globals at globals
  have database:=invariant.database.of_frame pure
  have scratch : ∃ cursor,post.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)):=⟨cursor,by rw [globals]; exact invariant.scratch.cursorGlobal⟩
  exact ⟨heap,child,returnedEq,by rw [globals]; exact invariant.heapCell,invariant.heapArena,invariant.heapBound,invariant.aligned,invariant.frontierBefore,scratch,invariant.tableBefore,database,
    owned.weaken post child (max frontier (resultLower [])) heap.toNat frontier heap.toNat (Nat.le_max_left _ _) (Nat.le_refl _)⟩

theorem Output.of_fields (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db : BitVec 64)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : Output databaseData frontier db source returned)
    (memory : target.memory=source.memory) (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (heap : target.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr"))
    (scratch : ∃ cursor,target.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor))) :
    Output databaseData frontier db target returned := by
  obtain ⟨actualHeap,child,returnedEq,heapCell,arena,bounded,aligned,grows,oldScratch,tableBefore,database,owned⟩:=output
  have databasePost:=database.of_before frontier tableBefore domain endian
    (fun query earlier=>congrFun memory query)
  exact ⟨actualHeap,child,returnedEq,heap.trans heapCell,arena,bounded,aligned,grows,scratch,tableBefore,databasePost,
    owned.of_fields source target child frontier actualHeap.toNat memory⟩

theorem Output.of_erase (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db : BitVec 64)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : Output databaseData frontier db source returned) (pure : Input.LocalEffects.erase target=Input.LocalEffects.erase source) :
    Output databaseData frontier db target returned := by
  have domain:=congrArg PanSemStateFiniteExact.memaddrs pure
  change target.memaddrs=source.memaddrs at domain
  have endian:=congrArg PanSemStateFiniteExact.be pure
  change target.be=source.be at endian
  have globals:=congrArg PanSemStateFiniteExact.globals pure
  change target.globals=source.globals at globals
  have saved:=output
  obtain ⟨actualHeap,child,returnedEq,heapCell,arena,bounded,aligned,grows,scratch,tableBefore,database,owned⟩:=saved
  obtain ⟨cursor,cursorCell⟩:=scratch
  exact output.of_fields databaseData frontier db source target returned (Input.LocalEffects.memory_of_erase source target pure) domain endian (by rw [globals])
    ⟨cursor,by rw [globals]; exact cursorCell⟩

theorem Output.release (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db mark : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : Output databaseData frontier db source returned) :
    Output databaseData frontier db (Arenas.Scratch.released {source with clock:=source.clock-1} mark) returned := by
  apply output.of_fields databaseData frontier db source (Arenas.Scratch.released {source with clock:=source.clock-1} mark) returned rfl rfl rfl
  · simp [Arenas.Scratch.released,HolFiniteMapExact.update,FUPDATE,show ofString "scratch_ptr"≠ofString "heap_ptr" from by decide]
  · exact ⟨mark,by simp [Arenas.Scratch.released,HolFiniteMapExact.update,FUPDATE]⟩

theorem Output.resume (databaseData : Input.CurrentTable.NodeBuild.Data) (frontier : Nat) (db : BitVec 64)
    (post target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : Output databaseData frontier db post returned) (pure : Input.LocalEffects.erase target=Input.LocalEffects.erase post)
    (dbCell : target.locals.lookup (ofString "db")=some (.val (.word db))) :
    ∃ heap child,returned=.val (.word child) ∧ Input.CurrentTable.NodeLookup.Database target databaseData ∧
      target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      AllocatedBytes.Arena heap 0 ∧ heap.toNat≤2952790016 ∧ heap.toNat%8=0 ∧ frontier≤heap.toNat ∧ ResultOwned target frontier heap.toNat child := by
  obtain ⟨heap,child,returnedEq,heapCell,arena,bounded,aligned,grows,scratch,tableBefore,database,owned⟩:=output.of_erase databaseData frontier db post target returned pure
  exact ⟨heap,child,returnedEq,database,heapCell,arena,bounded,aligned,grows,owned⟩

end InitECandidate.Solver.Mpt.WitnessMaterialize

#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.Output.of_completed
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.Output.of_fields
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.Output.of_erase
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.Output.release
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.Output.resume
