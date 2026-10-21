import InitECandidate.Solver.Input.WitnessResolveNormalFrame
import InitECandidate.Solver.Input.FrozenWitnessDatabases
import InitECandidate.Solver.Mpt.WitnessRecordIntervalFrame

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The actual whole resolver preserves every active record whose real
scratch address is above the incoming cursor and whose persistent data was
allocated before its incoming heap. This also applies to older stack frames. -/
theorem ResolveFrame.record_view (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor limit record db : BitVec 64) (data : Mpt.WitnessRecord.Description)
    (frame : ResolveFrame source target heap cursor limit)
    (view : Mpt.WitnessRecord.View source record db data) (before : data.BeforeHeap heap.toNat)
    (recordAbove : cursor.toNat≤record.toNat) (below : cursor.toNat≤2713717616) (heapLower : 2713731432≤heap.toNat) :
    Mpt.WitnessRecord.View target record db data := by
  have recordUpper:=view.ceiling
  have arrayLower:=view.arrayFloor
  have payloadLower:=view.payloadFloor
  exact view.interval_frame source target record db data cursor.toNat heap.toNat recordAbove (by omega)
    (by omega) before.1 (by omega) before.2 frame.domain frame.memory

/-- Restore both fixed witness databases across the same actual resolver
frame. Their fixed frontier can be below the evolving current heap. -/
theorem FrozenWitnessDatabases.resolve_frame (input : Guest.InputBlob)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit : BitVec 64) (frontier : Nat)
    (frozen : FrozenWitnessDatabases input source frontier) (frame : ResolveFrame source target heap cursor limit)
    (grows : frontier≤heap.toNat) (below : cursor.toNat≤2713717616)
    (dbCell : target.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "db")=source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "db")) :
    FrozenWitnessDatabases input target frontier :=
  frozen.frame input source target frontier frame.domain frame.endian dbCell
    (fun query lower upper=>frame.memory query (below.trans lower) (upper.trans_le grows))

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.ResolveFrame.record_view
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.FrozenWitnessDatabases.resolve_frame
