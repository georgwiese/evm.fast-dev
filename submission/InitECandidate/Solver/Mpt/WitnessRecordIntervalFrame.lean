import InitECandidate.Solver.Mpt.WitnessRecordView
import InitECandidate.Solver.Mpt.WitnessDecodeNormalFrame

namespace InitECandidate.Solver.Mpt.WitnessRecord
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- A live physical record needs agreement only on its own initialized
words, persistent rows and stage data. An interval containing those regions
is sufficient; unrelated scratch and later allocations may change. -/
theorem View.interval_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db : BitVec 64) (data : Description) (view : View source record db data) (lower upper : Nat)
    (recordLower : lower≤record.toNat) (recordUpper : record.toNat+88≤upper)
    (arrayLower : lower≤data.array.toNat) (arrayUpper : data.array.toNat+16*data.items.length≤upper)
    (payloadLower : lower≤data.payload.startAddress) (payloadUpper : data.payload.endAddress≤upper)
    (domain : target.memaddrs=source.memaddrs)
    (memory : ∀ query : BitVec 64,lower≤query.toNat→query.toNat<upper→target.memory query=source.memory query) :
    View target record db data := by
  have rows:=view.rows.frame source target data.array data.listPointer data.bytes data.items domain
    (fun query first last=>memory query (arrayLower.trans first) (last.trans_le arrayUpper))
  have cells : ∀ entry∈data.cells,target.memory (record+BitVec.ofNat 64 entry.1)=.word entry.2:=by
    intro entry member
    have geometry:=data.cells_geometry entry member
    have number:=byteAddress_toNat record entry.1 (by have bound:=view.arena.upper; omega)
    have first : lower≤(record+BitVec.ofNat 64 entry.1).toNat:=by change lower≤(byteAddress record entry.1).toNat; rw [number]; omega
    have last : (record+BitVec.ofNat 64 entry.1).toNat<upper:=by change (byteAddress record entry.1).toNat<upper; rw [number]; omega
    rw [memory _ first last]
    exact view.cells entry member
  have owned : data.payload.Owned target:=by
    have old:=view.owned
    cases payloadEq : data.payload with
    | extension nibbles length=>simpa only [payloadEq,Payload.Owned] using old
    | branch node index occupied=>
      simp only [payloadEq,Payload.Owned] at old ⊢
      have first : lower≤node.toNat:=by simpa only [payloadEq,Payload.startAddress] using payloadLower
      have last : node.toNat<upper:=by
        change data.payload.endAddress≤upper at payloadUpper
        rw [payloadEq] at payloadUpper
        change node.toNat+176≤upper at payloadUpper
        omega
      exact ⟨old.1,old.2.1,(memory node first last).trans old.2.2⟩
  exact ⟨view.arena,view.aligned,view.ceiling,view.arrayFloor,view.payloadFloor,cells,rows,view.count,
    view.parentBound,view.parentLower,view.parentBeforeDb,view.payloadLower,view.payloadUpper,owned,view.separated,view.scratchLower,view.persistent⟩

/-- An older record is above the incoming cursor while its persistent
rows and payload are below the incoming heap. The decoder's two-sided live
frame therefore preserves the whole physical view across new child work. -/
theorem View.live_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db heap cursor limit : BitVec 64) (data : Description) (view : View source record db data)
    (before : data.BeforeHeap heap.toNat) (older : cursor.toNat≤record.toNat)
    (frame : WitnessDecode.LiveFrame source target heap cursor limit) : View target record db data := by
  have domain : target.memaddrs=source.memaddrs:=frame.live.domain.trans view.rows.domain.symm
  have rows:=view.rows.earlier source target data.array data.listPointer data.bytes data.items heap.toNat before.1 domain frame.memoryBefore
  have cells : ∀ entry∈data.cells,target.memory (record+BitVec.ofNat 64 entry.1)=.word entry.2:=by
    intro entry member
    have geometry:=data.cells_geometry entry member
    have number:=byteAddress_toNat record entry.1 (by have bound:=view.arena.upper; omega)
    have above : cursor.toNat≤(record+BitVec.ofNat 64 entry.1).toNat:=by
      change cursor.toNat≤(byteAddress record entry.1).toNat
      rw [number]
      omega
    rw [frame.memoryAbove _ above]
    exact view.cells entry member
  have owned : data.payload.Owned target:=by
    have old:=view.owned
    cases payloadEq : data.payload with
    | extension nibbles length=>simpa only [payloadEq,Payload.Owned] using old
    | branch node index occupied=>
      simp only [payloadEq,Payload.Owned] at old ⊢
      have last:=before.2
      simp only [payloadEq,Payload.endAddress] at last
      exact ⟨old.1,old.2.1,(frame.memoryBefore node (by omega)).trans old.2.2⟩
  exact ⟨view.arena,view.aligned,view.ceiling,view.arrayFloor,view.payloadFloor,cells,rows,view.count,
    view.parentBound,view.parentLower,view.parentBeforeDb,view.payloadLower,view.payloadUpper,owned,view.separated,view.scratchLower,view.persistent⟩

end InitECandidate.Solver.Mpt.WitnessRecord

#print axioms InitECandidate.Solver.Mpt.WitnessRecord.View.interval_frame
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.View.live_frame
