import InitECandidate.Solver.Mpt.WitnessRecordView
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.Mpt.WitnessRecord
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The two real bounded scalar counter writes in an active branch. -/
inductive BranchCounter where
  | index (value : Fin 16)
  | occupied (value : Fin 17)
def BranchCounter.offset : BranchCounter→Nat | .index _=>32 | .occupied _=>40
def BranchCounter.word : BranchCounter→BitVec 64
  | .index value=>BitVec.ofNat 64 value.val | .occupied value=>BitVec.ofNat 64 value.val
def BranchCounter.nextIndex : BranchCounter→Fin 16→Fin 16 | .index value,_=>value | .occupied _,old=>old
def BranchCounter.nextOccupied : BranchCounter→Fin 17→Fin 17 | .index _,old=>old | .occupied value,_=>value
def BranchCounter.description (counter : BranchCounter) (data : Description) (node : BitVec 64) (index : Fin 16) (occupied : Fin 17) : Description:=
  {data with payload:=.branch node (counter.nextIndex index) (counter.nextOccupied occupied)}

theorem BranchCounter.geometry (counter : BranchCounter) : 0<counter.offset ∧ counter.offset+8≤88 ∧ counter.offset%8=0 := by
  cases counter <;> simp [BranchCounter.offset]

/-- Either actual counter write updates exactly the corresponding physical
descriptor field. All other initialized fields, persistent rows, node tag
and allocation separation are retained. -/
theorem View.branch_counter (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db node : BitVec 64)
    (data : Description) (index : Fin 16) (occupied : Fin 17) (counter : BranchCounter)
    (view : View source record db data) (payload : data.payload=.branch node index occupied) :
    View {source with memory:=StoreWord.put source.memory (record+BitVec.ofNat 64 counter.offset) counter.word}
      record db (counter.description data node index occupied) := by
  let target : PanSemStateFiniteExact 64 Guest.HostMemory:=
    {source with memory:=StoreWord.put source.memory (record+BitVec.ofNat 64 counter.offset) counter.word}
  let nextData:=counter.description data node index occupied
  have geometry:=counter.geometry
  have number : (record+BitVec.ofNat 64 counter.offset).toNat=record.toNat+counter.offset:=
    byteAddress_toNat record counter.offset (by have upper:=view.arena.upper; omega)
  have currentRows : WitnessDecode.Rows target data.array data.listPointer data.bytes data.items:=by
    apply view.rows.frame source target data.array data.listPointer data.bytes data.items rfl
    intro query lower upper
    have away : query≠record+BitVec.ofNat 64 counter.offset:=by
      intro same
      have numeric:=congrArg BitVec.toNat same
      have recordUpper:=view.ceiling
      have arrayLower:=view.arrayFloor
      omega
    exact if_neg away
  have currentCells : ∀ entry∈nextData.cells,target.memory (record+BitVec.ofNat 64 entry.1)=.word entry.2:=by
    intro entry member
    change StoreWord.put source.memory (record+BitVec.ofNat 64 counter.offset) counter.word (record+BitVec.ofNat 64 entry.1)=.word entry.2
    cases counter <;>
      simp only [nextData,BranchCounter.description,BranchCounter.nextIndex,BranchCounter.nextOccupied,Description.cells,
        BranchCounter.offset,BranchCounter.word,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
    all_goals
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals first
        | exact if_pos rfl
        | rw [StoreWord.put,if_neg (by simp [BitVec.add_right_inj])]
          exact view.cells _ (by simp [Description.cells,payload])
  have owned:=view.owned
  simp only [payload,Payload.Owned] at owned
  have nodeLower : 2713731432≤node.toNat:=by
    have lower:=view.payloadFloor
    simpa only [payload,Payload.startAddress] using lower
  have away : node≠record+BitVec.ofNat 64 counter.offset:=by
    intro same
    have numeric:=congrArg BitVec.toNat same
    have recordUpper:=view.ceiling
    omega
  have currentOwned : nextData.payload.Owned target:=
    ⟨owned.1,owned.2.1,(if_neg away).trans owned.2.2⟩
  have count : nextData.items.length=nextData.payload.count:=by
    simpa only [nextData,BranchCounter.description,payload,Payload.count] using view.count
  have separated : nextData.Separated:=by
    simpa only [nextData,BranchCounter.description,Description.Separated,payload] using view.separated
  exact ⟨view.arena,view.aligned,view.ceiling,view.arrayFloor,nodeLower,currentCells,currentRows,count,
    view.parentBound,view.parentLower,view.parentBeforeDb,view.payloadLower,view.payloadUpper,currentOwned,separated⟩

theorem BranchCounter.before_heap (counter : BranchCounter) (data : Description) (node : BitVec 64)
    (index : Fin 16) (occupied : Fin 17) (frontier : Nat) (payload : data.payload=.branch node index occupied)
    (before : data.BeforeHeap frontier) : (counter.description data node index occupied).BeforeHeap frontier := by
  simpa only [BranchCounter.description,Description.BeforeHeap,payload,Payload.endAddress] using before

/-- The original PREV and pending-HASH words survive either counter write. -/
theorem BranchCounter.auxiliary (counter : BranchCounter) (memory : BitVec 64→HolWordLab 64) (record : BitVec 64) :
    StoreWord.put memory (record+BitVec.ofNat 64 counter.offset) counter.word record=memory record ∧
      StoreWord.put memory (record+BitVec.ofNat 64 counter.offset) counter.word (record+80#64)=memory (record+80#64) := by
  cases counter <;> simp [StoreWord.put,BranchCounter.offset,BitVec.add_right_inj]

end InitECandidate.Solver.Mpt.WitnessRecord

#print axioms InitECandidate.Solver.Mpt.WitnessRecord.BranchCounter.geometry
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.View.branch_counter
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.BranchCounter.before_heap
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.BranchCounter.auxiliary
