import InitECandidate.Solver.Mpt.WitnessDecodeNormalFrame
import InitECandidate.Solver.Input.FrozenWitnessDatabases
import InitECandidate.Solver.Mpt.WitnessRecordIntervalFrame
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem NormalFrame.store_below (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor limit address word : BitVec 64) (frame : NormalFrame source target heap cursor limit)
    (below : address.toNat<cursor.toNat) :
    NormalFrame source {target with memory:=StoreWord.put target.memory address word} heap cursor limit := by
  obtain ⟨next,scratch,drops⟩:=frame.nextScratch
  refine ⟨frame.nextHeap,⟨next,scratch.of_fields target _ next limit rfl rfl,drops⟩,frame.domain,frame.endian,frame.code,frame.globals,?_⟩
  intro query above before
  have away : query≠address:=by intro same; have numeric:=congrArg BitVec.toNat same; omega
  change StoreWord.put target.memory address word query=source.memory query
  rw [StoreWord.put,if_neg away]
  exact frame.memory query above before

theorem NormalFrame.record_view (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor limit record db : BitVec 64) (data : WitnessRecord.Description)
    (frame : NormalFrame source target heap cursor limit) (view : WitnessRecord.View source record db data)
    (before : data.BeforeHeap heap.toNat) (recordAbove : cursor.toNat≤record.toNat)
    (below : cursor.toNat≤2713717616) (heapLower : 2713731432≤heap.toNat) : WitnessRecord.View target record db data := by
  have recordUpper:=view.ceiling
  have arrayLower:=view.arrayFloor
  have payloadLower:=view.payloadFloor
  exact view.interval_frame source target record db data cursor.toNat heap.toNat recordAbove (by omega)
    (by omega) before.1 (by omega) before.2 frame.domain frame.memory

end InitECandidate.Solver.Mpt.WitnessDecode

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem FrozenWitnessDatabases.decode_frame (input : Guest.InputBlob)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit : BitVec 64) (frontier : Nat)
    (frozen : FrozenWitnessDatabases input source frontier) (frame : Mpt.WitnessDecode.NormalFrame source target heap cursor limit)
    (grows : frontier≤heap.toNat) (below : cursor.toNat≤2713717616)
    (dbCell : target.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "db")=source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "db")) :
    FrozenWitnessDatabases input target frontier :=
  frozen.frame input source target frontier frame.domain frame.endian dbCell
    (fun query lower upper=>frame.memory query (below.trans lower) (upper.trans_le grows))

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.NormalFrame.store_below
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.NormalFrame.record_view
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.FrozenWitnessDatabases.decode_frame
