import InitECandidate.Solver.Input.RootBoundaryMemoryFrame
import InitECandidate.Solver.Input.OriginalScalarGlobals
import InitECandidate.Solver.Rlp.SlicesSnapshotLocal

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The genuinely returned list array advances the heap while temporary
scratch and fresh-array writes leave both original database bands intact. -/
theorem RootBoundary.slices_frame (input : Guest.InputBlob) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit count : BitVec 64) (items : List Rlp.ListItem)
    (actual : RootBoundary input source)
    (sourceHeap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (below : cursor.toNat≤2713717616)
    (snapshot : Rlp.Slices.Snapshot (LocalEffects.erase source) target pointer length heap cursor limit count items)
    (db : target.locals.lookup (ofString "db")=source.locals.lookup (ofString "db")) : RootBoundary input target := by
  apply actual.memory_frame input source target heap (PersistentAlloc.rounded heap (count*16#64)) sourceHeap snapshot.heapCell snapshot.nextArena snapshot.nextAligned
    (by have grows:=snapshot.grows; omega) snapshot.domain.symm snapshot.endian.symm db
  intro query lower upper
  exact snapshot.memory query (below.trans lower) (Or.inl upper)

theorem slices_scalar_globals (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit count : BitVec 64) (items : List Rlp.ListItem)
    (snapshot : Rlp.Slices.Snapshot (LocalEffects.erase source) target pointer length heap cursor limit count items)
    (scalars : OriginalScalarGlobals.Scalars source.globals) : OriginalScalarGlobals.Scalars target.globals := by
  intro key member
  by_cases changed : key=ofString "heap_ptr"
  · subst key
    exact ⟨PersistentAlloc.rounded heap (count*16#64),snapshot.heapCell⟩
  · obtain ⟨word,cell⟩:=scalars key member
    exact ⟨word,(snapshot.globals key changed).trans cell⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.RootBoundary.slices_frame
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.slices_scalar_globals
