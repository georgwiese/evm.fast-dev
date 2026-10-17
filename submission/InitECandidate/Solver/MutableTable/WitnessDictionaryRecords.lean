import InitECandidate.Solver.MutableTable.WitnessBuildRecords
import InitECandidate.Solver.MutableTable.WitnessBuildHistory
import InitECandidate.Solver.MutableTable.DictionaryData

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
attribute [local instance] Classical.propDecidable

def recordSlices (plan : AllocatedLayout.Plan) (slices : Nat→Graph.Slice) (record : BitVec 64) : Graph.Slice:=
  slices ((record.toNat-plan.records)/16)

theorem recordSlices_address (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (slices : Nat→Graph.Slice)
    (i : Nat) (inside : i<plan.count) : recordSlices plan slices (recordAddress plan i)=slices i := by
  unfold recordSlices
  have first : recordAddress plan i=recordCell plan i 0:=by simpa only [BitVec.add_zero] using record_address plan i 0
  rw [first,record_number plan ready i 0 inside (by decide)]
  congr 1
  omega

theorem record_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain) (i offset : Nat)
    (inside : i<plan.count) (field : offset=0 ∨ offset=8) : source.memaddrs (recordAddress plan i+BitVec.ofNat 64 offset) := by
  rw [record_address,record_backing]
  rcases field with rfl|rfl <;>
    exact AllocatedLayout.mapped source plan ready domain .records _ (by omega) (by change _≤16*plan.count;omega)

/-- Every last-record-wins dictionary value has its actual mapped pointer/
length words, derived from constructor history and preserved slice records. -/
theorem history_value_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain) (slices : Nat→Graph.Slice)
    (input : List (Find.Key32×BitVec 64)) (history : History plan input) (records : Records source plan slices)
    (query : Find.Key32) (record : BitVec 64) (found : lastValue query input=some record) :
    source.memaddrs record ∧ source.memaddrs (record+8#64) ∧
      source.memory record=.word (recordSlices plan slices record).1 ∧ source.memory (record+8#64)=.word (recordSlices plan slices record).2 := by
  obtain ⟨i,inside,rfl⟩:=History.value_record plan input history query record (DictionaryData.lastValue_member query input record found)
  have first : recordAddress plan i=recordCell plan i 0:=by simpa only [BitVec.add_zero] using record_address plan i 0
  refine ⟨?_,record_mapped source plan ready domain i 8 inside (Or.inr rfl),?_,?_⟩
  · simpa only [BitVec.add_zero] using record_mapped source plan ready domain i 0 inside (Or.inl rfl)
  · rw [recordSlices_address plan ready slices i inside,first]
    exact records.pointers i inside
  · rw [recordSlices_address plan ready slices i inside,record_address]
    exact records.lengths i inside

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.recordSlices_address
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.history_value_cells
