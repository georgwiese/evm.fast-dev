import InitECandidate.Solver.Mpt.WitnessRecordView
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.Mpt.WitnessRecord
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Installing the real PREV link at0 preserves every initialized record
field and its persistent rows/nibble/branch ownership. No prior value for
PREV or HASH is assumed in the incoming record view. -/
theorem View.linked (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db previous : BitVec 64) (data : Description) (view : View source record db data) :
    View {source with memory:=StoreWord.put source.memory record previous} record db data := by
  let target : PanSemStateFiniteExact 64 Guest.HostMemory:={source with memory:=StoreWord.put source.memory record previous}
  have currentRows : WitnessDecode.Rows target data.array data.listPointer data.bytes data.items:=by
    apply view.rows.frame source target data.array data.listPointer data.bytes data.items rfl
    intro query lower upper
    have away : query≠record:=by
      intro same
      subst query
      have arrayBefore:=view.array_before_record source record db data
      omega
    exact if_neg away
  have currentCells : ∀ entry∈data.cells,target.memory (record+BitVec.ofNat 64 entry.1)=.word entry.2:=by
    intro entry member
    have geometry:=data.cells_geometry entry member
    have number:=byteAddress_toNat record entry.1 (by have upper:=view.arena.upper; omega)
    have away : record+BitVec.ofNat 64 entry.1≠record:=by
      intro same
      have numeric:=congrArg BitVec.toNat same
      change (byteAddress record entry.1).toNat=record.toNat at numeric
      rw [number] at numeric
      omega
    change StoreWord.put source.memory record previous (record+BitVec.ofNat 64 entry.1)=.word entry.2
    rw [StoreWord.put,if_neg away]
    exact view.cells entry member
  have owned : data.payload.Owned target:=by
    have old:=view.owned
    cases payloadEq : data.payload with
    | extension nibbles length=>simpa only [payloadEq,Payload.Owned] using old
    | branch node index occupied=>
      have payloadBefore:=view.payload_before_record source record db data
      simp only [payloadEq,Payload.endAddress] at payloadBefore
      have away : node≠record:=by
        intro same
        subst node
        omega
      simp only [payloadEq,Payload.Owned] at old ⊢
      refine ⟨old.1,old.2.1,?_⟩
      change StoreWord.put source.memory record previous node=.word 3#64
      rw [StoreWord.put,if_neg away]
      exact old.2.2
  exact ⟨view.arena,view.aligned,view.ceiling,view.arrayFloor,view.payloadFloor,currentCells,currentRows,view.count,
    view.parentBound,view.parentLower,view.parentBeforeDb,view.payloadLower,view.payloadUpper,owned,view.separated,view.scratchLower,view.persistent⟩

end InitECandidate.Solver.Mpt.WitnessRecord

#print axioms InitECandidate.Solver.Mpt.WitnessRecord.View.linked
