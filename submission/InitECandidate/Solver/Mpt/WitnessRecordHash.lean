import InitECandidate.Solver.Mpt.WitnessRecordView
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.Mpt.WitnessRecord
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem Description.cells_before_hash (data : Description) : ∀ entry∈data.cells,entry.1<80 := by
  cases payloadEq : data.payload <;> simp [Description.cells,payloadEq]

/-- The original core installs HASH at80 only after resolving a child.
This real store preserves all initialized stage fields, row cells and
owned persistent payload, independently of the previous HASH contents. -/
theorem View.hashed (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db hash : BitVec 64) (data : Description) (view : View source record db data) :
    View {source with memory:=StoreWord.put source.memory (record+80#64) hash} record db data := by
  let target : PanSemStateFiniteExact 64 Guest.HostMemory:={source with memory:=StoreWord.put source.memory (record+80#64) hash}
  have hashNumber : (record+80#64).toNat=record.toNat+80:=by
    simpa only [byteAddress] using byteAddress_toNat record 80 (by have upper:=view.arena.upper; omega)
  have currentRows : WitnessDecode.Rows target data.array data.listPointer data.bytes data.items:=by
    apply view.rows.frame source target data.array data.listPointer data.bytes data.items rfl
    intro query lower upper
    have away : query≠record+80#64:=by
      intro same
      have numeric:=congrArg BitVec.toNat same
      have recordBound:=view.ceiling
      have arrayBound:=view.arrayFloor
      omega
    exact if_neg away
  have currentCells : ∀ entry∈data.cells,target.memory (record+BitVec.ofNat 64 entry.1)=.word entry.2:=by
    intro entry member
    have geometry:=data.cells_before_hash entry member
    have number:=byteAddress_toNat record entry.1 (by have upper:=view.arena.upper; omega)
    have away : record+BitVec.ofNat 64 entry.1≠record+80#64:=by
      intro same
      have numeric:=congrArg BitVec.toNat same
      change (byteAddress record entry.1).toNat=(record+80#64).toNat at numeric
      rw [number,hashNumber] at numeric
      omega
    change StoreWord.put source.memory (record+80#64) hash (record+BitVec.ofNat 64 entry.1)=.word entry.2
    rw [StoreWord.put,if_neg away]
    exact view.cells entry member
  have owned : data.payload.Owned target:=by
    have old:=view.owned
    cases payloadEq : data.payload with
    | extension nibbles length=>simpa only [payloadEq,Payload.Owned] using old
    | branch node index occupied=>
      have floor:=view.payloadFloor
      change 2713731432≤data.payload.startAddress at floor
      rw [payloadEq] at floor
      change 2713731432≤node.toNat at floor
      have away : node≠record+80#64:=by
        intro same
        have numeric:=congrArg BitVec.toNat same
        have upper:=view.ceiling
        omega
      simp only [payloadEq,Payload.Owned] at old ⊢
      refine ⟨old.1,old.2.1,?_⟩
      change StoreWord.put source.memory (record+80#64) hash node=.word 3#64
      rw [StoreWord.put,if_neg away]
      exact old.2.2
  exact ⟨view.arena,view.aligned,view.ceiling,view.arrayFloor,view.payloadFloor,currentCells,currentRows,view.count,
    view.parentBound,view.parentLower,view.parentBeforeDb,view.payloadLower,view.payloadUpper,owned,view.separated⟩

theorem View.hash_preserves_previous (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db hash : BitVec 64) (data : Description) (view : View source record db data) :
    StoreWord.put source.memory (record+80#64) hash record=source.memory record := by
  have number : (record+80#64).toNat=record.toNat+80:=by
    simpa only [byteAddress] using byteAddress_toNat record 80 (by have upper:=view.arena.upper; omega)
  have away : record≠record+80#64:=by
    intro same
    have numeric:=congrArg BitVec.toNat same
    omega
  exact if_neg away

end InitECandidate.Solver.Mpt.WitnessRecord

#print axioms InitECandidate.Solver.Mpt.WitnessRecord.Description.cells_before_hash
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.View.hashed
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.View.hash_preserves_previous
