import InitECandidate.Solver.Rlp.SlicesSnapshotCall
import InitECandidate.Solver.Input.CallResumeFields

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Local scopes and caller restoration retain the current physical slice
snapshot. All byte provenance and rows are transported through the actual
nonlocal frame, without re-parsing or assuming a later successful read. -/
theorem Snapshot.of_erase (origin source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit count : BitVec 64) (items : List ListItem)
    (snapshot : Snapshot origin source pointer length heap cursor limit count items)
    (frame : Input.LocalEffects.erase target=Input.LocalEffects.erase source) :
    Snapshot origin target pointer length heap cursor limit count items := by
  have memory:=Input.LocalEffects.memory_of_erase source target frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  have endian:=congrArg PanSemStateFiniteExact.be frame
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change target.globals=source.globals at globals
  have code:=congrArg PanSemStateFiniteExact.code frame
  have exceptions:=congrArg PanSemStateFiniteExact.eshapes frame
  have oracle:=congrArg (fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>current.ffi.oracle) frame
  have model:=ListItems.transport source target pointer length.toNat items snapshot.itemModel length.isLt (by
    intro offset inside
    have read:=congrArg (fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>ReadLength.byte current (pointer+offset)) frame
    exact read.symm)
  refine ⟨model,snapshot.countExact,snapshot.countBound,?_,snapshot.arrayArena,snapshot.arrayAligned,
    Validation.Arena.of_fields source target cursor limit snapshot.arena domain globals,?_,snapshot.nextArena,snapshot.nextAligned,snapshot.grows,
    domain.trans snapshot.domain,endian.trans snapshot.endian,code.trans snapshot.code,exceptions.trans snapshot.exceptions,oracle.trans snapshot.oracle,?_,?_⟩
  · rw [memory]
    exact snapshot.records
  · rw [globals]
    exact snapshot.heapCell
  · intro key other
    rw [globals]
    exact snapshot.globals key other
  · intro query below outside
    rw [memory]
    exact snapshot.memory query below outside

theorem Snapshot.resumed (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit count : BitVec 64) (items : List ListItem) (name : String)
    (snapshot : Snapshot (Input.LocalEffects.erase source) target pointer length heap cursor limit count items) :
    Snapshot (Input.LocalEffects.erase source) (Input.CallNormal.continuationEntry source target name (result heap count)) pointer length heap cursor limit count items :=
  snapshot.of_erase _ target _ pointer length heap cursor limit count items (Input.CallNormal.continuation_erase source target name _)

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.Snapshot.of_erase
#print axioms InitECandidate.Solver.Rlp.Slices.Snapshot.resumed
