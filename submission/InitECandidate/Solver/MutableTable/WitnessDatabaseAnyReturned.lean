import InitECandidate.Solver.MutableTable.WitnessDatabaseAnyCost
import InitECandidate.Solver.MutableTable.WitnessOccupiedRecord

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
attribute [local instance] Classical.propDecidable

/-- Every actual normal database lookup returns an original bounded witness
slice or absence, even for arbitrary query pointers. Physical provenance
and constructor history provide the slice's real arena and address bounds. -/
theorem Database.any_body_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (array table : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (scratch query : BitVec 64) (actual : Database source array table count maximum slices scratch)
    (installed : Input.OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word table)))
    (hashCell : source.locals.lookup (ofString "hash")=some (.val (.word query)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source NodeDb.body=(some (.returned value),post)) :
    ∃ answer,value=NodeDb.output answer ∧ Input.LocalEffects.erase post=Input.LocalEffects.erase source ∧ source.clock-post.clock≤6*count+3 ∧
      (∀ slice,answer=some slice→∃ index<count,slice=slices index ∧ slice.2.toNat≤maximum ∧
        AllocatedBytes.Arena slice.1 slice.2.toNat ∧ 2713731432≤slice.1.toNat ∧ slice.1.toNat+slice.2.toNat≤table.toNat) := by
  obtain ⟨bits,stored,input,logical,lower,upper,capacity,ready,built,history,length,rows⟩ := actual.data
  let plan:=Constructor.allocationPlan (effectiveRecords array table count) table.toNat count (2^bits)
  obtain ⟨order,bounded,runtime⟩ := runtime_of_built source plan ready actual.domain bits (by omega) rfl scratch stored input logical built history query
  have records (record : BitVec 64) (selected : OccupiedRecord source plan query record) :
      source.memaddrs record ∧ source.memaddrs (record+8#64) ∧
      source.memory record=.word (recordSlices plan slices record).1 ∧ source.memory (record+8#64)=.word (recordSlices plan slices record).2 := by
    obtain ⟨key,found⟩ := occupied_record_key source plan bits (by omega) rfl scratch stored input logical built query record selected
    exact history_value_cells source plan ready actual.domain slices input history rows key record found
  obtain ⟨answer,valueEq,selected⟩ := runtime_lookup_returned source post plan query bits order runtime installed
    (by simpa only [plan,Constructor.allocationPlan,BitVec.ofNat_toNat,BitVec.setWidth_eq] using dbCell) hashCell (recordSlices plan slices) records value normal
  have pure:=Database.any_body_readonly source installed source rfl
  rw [normal] at pure
  have price:=actual.any_body_cost source array table count maximum slices scratch query installed dbCell hashCell
  rw [normal] at price
  refine ⟨answer.map (recordSlices plan slices),valueEq,pure,price,?_⟩
  intro slice found
  cases answer with
  | none => simp only [Option.map_none] at found; cases found
  | some record =>
    have sliceEq : recordSlices plan slices record=slice := Option.some.inj found
    obtain ⟨key,recordFound⟩ := occupied_record_key source plan bits (by omega) rfl scratch stored input logical built query record (selected record rfl)
    obtain ⟨index,inside,address⟩ := history.value_record plan input key record (DictionaryData.lastValue_member key input record recordFound)
    have equal : slice=slices index := by
      rw [← sliceEq,address,recordSlices_address plan ready slices index inside]
    exact ⟨index,inside,equal,by rw [equal]; exact actual.sizes index inside,
      by rw [equal]; exact actual.arenas index inside,by rw [equal]; exact actual.sourceLower index inside,
      by rw [equal]; exact actual.sourceBefore index inside⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Database.any_body_returned
