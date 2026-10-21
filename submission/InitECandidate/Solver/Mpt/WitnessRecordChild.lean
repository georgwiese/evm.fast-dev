import InitECandidate.Solver.Mpt.WitnessRecordView
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.Mpt.WitnessRecord
open Flapjack PanSemStateFiniteExact WitnessRadix

def childAddress (node : BitVec 64) (index : Fin 16) : BitVec 64:=byteAddress node (32+8*index.val)

theorem View.branch_rows_before (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db node : BitVec 64)
    (data : Description) (index : Fin 16) (occupied : Fin 17) (view : View source record db data)
    (payload : data.payload=.branch node index occupied) : data.array.toNat+16*data.items.length≤node.toNat := by
  have before:=view.separated
  simpa only [Description.Separated,payload] using before

theorem View.branch_child_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db node : BitVec 64)
    (data : Description) (index : Fin 16) (occupied : Fin 17) (view : View source record db data)
    (payload : data.payload=.branch node index occupied) : source.memaddrs (childAddress node index) := by
  have owned:=view.owned
  simp only [payload,Payload.Owned] at owned
  have inside:=index.isLt
  exact AllocatedBytes.word_mapped source node 176 (32+8*index.val) view.rows.domain owned.1 (by omega) owned.2.1 (by omega)

/-- A positive in-node word store preserves the activation record,
its earlier row array and the branch tag. This covers child, value and
parent-metadata stores in the actual original return paths. -/
theorem View.branch_store (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db node value : BitVec 64)
    (data : Description) (index : Fin 16) (occupied : Fin 17) (offset : Nat)
    (positive : 0<offset) (inside : offset+8≤176) (view : View source record db data)
    (payload : data.payload=.branch node index occupied) :
    View {source with memory:=StoreWord.put source.memory (byteAddress node offset) value} record db data := by
  let target : PanSemStateFiniteExact 64 Guest.HostMemory:={source with memory:=StoreWord.put source.memory (byteAddress node offset) value}
  have owned:=view.owned
  simp only [payload,Payload.Owned] at owned
  have nodeArena:=owned.1
  have number : (byteAddress node offset).toNat=node.toNat+offset:=
    byteAddress_toNat node offset (by have upper:=nodeArena.upper; omega)
  have arrayBefore:=view.branch_rows_before source record db node data index occupied payload
  have currentRows : WitnessDecode.Rows target data.array data.listPointer data.bytes data.items:=by
    apply view.rows.frame source target data.array data.listPointer data.bytes data.items rfl
    intro query lower upper
    have away : query≠byteAddress node offset:=by
      intro same
      have numeric:=congrArg BitVec.toNat same
      omega
    exact if_neg away
  have nodeFloor : 2713731432≤node.toNat:=by
    have lower:=view.payloadFloor
    simpa only [payload,Payload.startAddress] using lower
  have currentCells : ∀ entry∈data.cells,target.memory (record+BitVec.ofNat 64 entry.1)=.word entry.2:=by
    intro entry member
    have geometry:=data.cells_geometry entry member
    have cellNumber:=byteAddress_toNat record entry.1 (by have upper:=view.arena.upper; omega)
    have away : record+BitVec.ofNat 64 entry.1≠byteAddress node offset:=by
      intro same
      have numeric:=congrArg BitVec.toNat same
      change (byteAddress record entry.1).toNat=(byteAddress node offset).toNat at numeric
      rw [cellNumber,number] at numeric
      have ceiling:=view.ceiling
      omega
    change StoreWord.put source.memory (byteAddress node offset) value (record+BitVec.ofNat 64 entry.1)=.word entry.2
    rw [StoreWord.put,if_neg away]
    exact view.cells entry member
  have tagAway : node≠byteAddress node offset:=by
    intro same
    have numeric:=congrArg BitVec.toNat same
    omega
  have currentOwned : data.payload.Owned target:=by
    simp only [payload,Payload.Owned]
    exact ⟨owned.1,owned.2.1,(if_neg tagAway).trans owned.2.2⟩
  exact ⟨view.arena,view.aligned,view.ceiling,view.arrayFloor,view.payloadFloor,currentCells,currentRows,view.count,
    view.parentBound,view.parentLower,view.parentBeforeDb,view.payloadLower,view.payloadUpper,currentOwned,view.separated⟩

/-- The real child slot is a positive word of the owned branch node. -/
theorem View.branch_child (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db node child : BitVec 64)
    (data : Description) (index : Fin 16) (occupied : Fin 17) (view : View source record db data)
    (payload : data.payload=.branch node index occupied) :
    View {source with memory:=StoreWord.put source.memory (childAddress node index) child} record db data := by
  have bound:=index.isLt
  exact view.branch_store source record db node child data index occupied (32+8*index.val) (by omega) (by omega) payload

end InitECandidate.Solver.Mpt.WitnessRecord

#print axioms InitECandidate.Solver.Mpt.WitnessRecord.View.branch_rows_before
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.View.branch_child_mapped
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.View.branch_store
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.View.branch_child
