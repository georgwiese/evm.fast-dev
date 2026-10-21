import InitECandidate.Solver.Mpt.WitnessRecordView

namespace InitECandidate.Solver.Mpt.WitnessRecord
open Flapjack PanSemStateFiniteExact

/-- Actual local/clock/caller changes retain the physical record view when
its memory and ordinary domain are unchanged. -/
theorem View.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db : BitVec 64) (data : Description) (view : View source record db data)
    (memory : target.memory=source.memory) (domain : target.memaddrs=source.memaddrs) : View target record db data := by
  have rows:=view.rows.frame source target data.array data.listPointer data.bytes data.items domain
    (fun query lower upper=>congrFun memory query)
  have cells : ∀ entry∈data.cells,target.memory (record+BitVec.ofNat 64 entry.1)=.word entry.2:=by
    intro entry member
    rw [memory]
    exact view.cells entry member
  have owned : data.payload.Owned target:=by
    have old:=view.owned
    cases payloadEq : data.payload <;> simpa only [payloadEq,Payload.Owned,memory] using old
  exact ⟨view.arena,view.aligned,view.ceiling,view.arrayFloor,view.payloadFloor,cells,rows,view.count,
    view.parentBound,view.parentLower,view.parentBeforeDb,view.payloadLower,view.payloadUpper,owned⟩

end InitECandidate.Solver.Mpt.WitnessRecord

#print axioms InitECandidate.Solver.Mpt.WitnessRecord.View.of_fields
