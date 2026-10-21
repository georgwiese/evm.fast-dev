import InitECandidate.Solver.Mpt.WitnessCoreBodyNormal
import InitECandidate.Solver.Arenas.ScratchScope

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessCore WitnessCore.Stack Input.Main.RunAttemptConstructors

/-- Physical materializer output, independent of cleared callee locals
and the scratch cursor restored by its wrappers. The normalized db local
only names the retained physical database; genuine caller db is checked
when re-establishing the actual caller boundary. -/
def Output (input : Guest.InputBlob) (frontier : Nat) (db : BitVec 64)
    (post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64) : Prop:=
  ∃ heap child,returned=.val (.word child) ∧
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
    AllocatedBytes.Arena heap 0 ∧ heap.toNat%8=0 ∧ frontier≤heap.toNat ∧
    (∃ cursor,post.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor))) ∧
    FrozenWitnessDatabases input (QueryBranch.bind post "db" db) frontier ∧ ResultOwned post frontier heap.toNat child

theorem Output.of_completed (input : Guest.InputBlob) (frontier : Nat) (db limit : BitVec 64)
    (post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (completed : Completed input frontier db limit post returned) : Output input frontier db post returned := by
  obtain ⟨heap,cursor,child,finished,returnedEq,invariant,pure,owned⟩:=completed
  have memory:=Input.LocalEffects.memory_of_erase finished post pure
  have domain:=congrArg PanSemStateFiniteExact.memaddrs pure
  change post.memaddrs=finished.memaddrs at domain
  have endian:=congrArg PanSemStateFiniteExact.be pure
  change post.be=finished.be at endian
  have globals:=congrArg PanSemStateFiniteExact.globals pure
  change post.globals=finished.globals at globals
  have frozen:=invariant.frozen.frame input finished (QueryBranch.bind post "db" db) frontier domain endian
    ((bind_lookup_same post "db" db).trans invariant.dbCell.symm) (by intros; exact congrFun memory _)
  have scratch : ∃ cursor,post.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)):=⟨cursor,by rw [globals]; exact invariant.scratch.cursorGlobal⟩
  exact ⟨heap,child,returnedEq,by rw [globals]; exact invariant.heapCell,invariant.heapArena,invariant.aligned,invariant.frontierBefore,scratch,frozen,
    owned.weaken post child (max frontier (resultLower [])) heap.toNat frontier heap.toNat (Nat.le_max_left _ _) (Nat.le_refl _)⟩

theorem Output.of_fields (input : Guest.InputBlob) (frontier : Nat) (db : BitVec 64)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : Output input frontier db source returned)
    (memory : target.memory=source.memory) (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (heap : target.globals.lookup (ofString "heap_ptr")=source.globals.lookup (ofString "heap_ptr"))
    (scratch : ∃ cursor,target.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor))) :
    Output input frontier db target returned := by
  obtain ⟨actualHeap,child,returnedEq,heapCell,arena,aligned,grows,oldScratch,frozen,owned⟩:=output
  have frozenPost:=frozen.frame input (QueryBranch.bind source "db" db) (QueryBranch.bind target "db" db) frontier domain endian
    ((bind_lookup_same target "db" db).trans (bind_lookup_same source "db" db).symm) (by intros; exact congrFun memory _)
  exact ⟨actualHeap,child,returnedEq,heap.trans heapCell,arena,aligned,grows,scratch,frozenPost,
    owned.of_fields source target child frontier actualHeap.toNat memory⟩

theorem Output.of_erase (input : Guest.InputBlob) (frontier : Nat) (db : BitVec 64)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : Output input frontier db source returned) (pure : Input.LocalEffects.erase target=Input.LocalEffects.erase source) :
    Output input frontier db target returned := by
  have domain:=congrArg PanSemStateFiniteExact.memaddrs pure
  change target.memaddrs=source.memaddrs at domain
  have endian:=congrArg PanSemStateFiniteExact.be pure
  change target.be=source.be at endian
  have globals:=congrArg PanSemStateFiniteExact.globals pure
  change target.globals=source.globals at globals
  have saved:=output
  obtain ⟨actualHeap,child,returnedEq,heapCell,arena,aligned,grows,scratch,frozen,owned⟩:=saved
  obtain ⟨cursor,cursorCell⟩:=scratch
  exact output.of_fields input frontier db source target returned (Input.LocalEffects.memory_of_erase source target pure) domain endian (by rw [globals])
    ⟨cursor,by rw [globals]; exact cursorCell⟩

theorem Output.release (input : Guest.InputBlob) (frontier : Nat) (db mark : BitVec 64)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : Output input frontier db source returned) :
    Output input frontier db (Arenas.Scratch.released {source with clock:=source.clock-1} mark) returned := by
  apply output.of_fields input frontier db source (Arenas.Scratch.released {source with clock:=source.clock-1} mark) returned rfl rfl rfl
  · simp [Arenas.Scratch.released,HolFiniteMapExact.update,FUPDATE,show ofString "scratch_ptr"≠ofString "heap_ptr" from by decide]
  · exact ⟨mark,by simp [Arenas.Scratch.released,HolFiniteMapExact.update,FUPDATE]⟩

theorem Output.resume (input : Guest.InputBlob) (frontier : Nat) (db : BitVec 64)
    (post target : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (output : Output input frontier db post returned) (pure : Input.LocalEffects.erase target=Input.LocalEffects.erase post)
    (dbCell : target.locals.lookup (ofString "db")=some (.val (.word db))) :
    ∃ heap child,returned=.val (.word child) ∧ RootBoundary input target ∧
      target.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ ResultOwned target frontier heap.toNat child := by
  obtain ⟨heap,child,returnedEq,heapCell,arena,aligned,grows,scratch,frozen,owned⟩:=output.of_erase input frontier db post target returned pure
  have frozenTarget:=frozen.frame input (QueryBranch.bind target "db" db) target frontier rfl rfl
    (dbCell.trans (bind_lookup_same target "db" db).symm) (by intros; rfl)
  exact ⟨heap,child,returnedEq,frozenTarget.boundary input target frontier heap heapCell arena aligned grows,heapCell,owned⟩

end InitECandidate.Solver.Mpt.WitnessMaterialize

#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.Output.of_completed
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.Output.of_fields
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.Output.of_erase
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.Output.release
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.Output.resume
