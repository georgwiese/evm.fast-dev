import InitECandidate.Solver.MutableTable.WitnessDatabase
import InitECandidate.Solver.MutableTable.NodeDbOriginalCode

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
attribute [local instance] Classical.propDecidable

/-- Every represented hit is one of the actual decoded witness slices;
this follows from insertion history even when hashes repeat or collide. -/
theorem sliceEntries_hit (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan)
    (slices : Nat→Graph.Slice) (input : List (Find.Key32×BitVec 64)) (history : History plan input)
    (query : Find.Key32) (slice : Graph.Slice) (found : lastValue query (sliceEntries plan slices input)=some slice) :
    ∃ index<plan.count,slice=slices index := by
  have member:=DictionaryData.lastValue_member query (sliceEntries plan slices input) slice found
  obtain ⟨entry,member,equal⟩ := List.mem_map.mp member
  obtain ⟨index,inside,address⟩ := history.value_record plan input entry.1 entry.2 member
  have value:=congrArg Prod.snd equal
  change recordSlices plan slices entry.2=slice at value
  rw [address,recordSlices_address plan ready slices index inside] at value
  exact ⟨index,inside,value.symm⟩

/-- Actual original lookup execution from a current constructor-derived
database, with a count-dependent probe price and genuine bounded hit data. -/
theorem Database.execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array table : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (scratch queryPointer : BitVec 64)
    (actual : Database source array table count maximum slices scratch)
    (installed : Input.OriginalCode.Installed source.code)
    (query : Find.Key32) (view : MemoryBytes.ByteView source queryPointer query) (fits : queryPointer.toNat+32<2^64)
    (dbLocal : source.locals.lookup (ofString "db")=some (.val (.word table)))
    (hashLocal : source.locals.lookup (ofString "hash")=some (.val (.word queryPointer)))
    (enough : 6*count+3≤source.clock) :
    ∃ answer paid target,paid≤6*count+3 ∧
      evaluateHOLFiniteState source NodeDb.body=(some (.returned (NodeDb.output answer)),target) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-paid} ∧
      (∀ slice,answer=some slice→∃ index<count,slice=slices index ∧ slice.2.toNat≤maximum ∧
        AllocatedBytes.Arena slice.1 slice.2.toNat ∧ 2713731432≤slice.1.toNat ∧ slice.1.toNat+slice.2.toNat≤table.toNat) := by
  obtain ⟨bits,stored,input,logical,lower,upper,capacity,ready,built,history,length,rows⟩ := actual.data
  let plan:=Constructor.allocationPlan (effectiveRecords array table count) table.toNat count (2^bits)
  have helpers:=original_helpers source.code installed
  obtain ⟨paid,target,price,run,frame⟩ := dictionary_lookup source _ ready actual.domain bits (by omega) rfl scratch stored input logical built history slices rows queryPointer query view fits actual.little
    (by simpa only [Constructor.allocationPlan,BitVec.ofNat_toNat,BitVec.setWidth_eq] using dbLocal) hashLocal helpers.hashCode helpers.compareCode helpers.findCode
    (NodeDb.original_get_code source.code installed) (by rw [length]; exact enough)
  refine ⟨lastValue query (sliceEntries plan slices input),paid,target,by rwa [length] at price,?_,frame,?_⟩
  · simpa only [lookup_output] using run
  · intro slice found
    obtain ⟨index,inside,equal⟩ := sliceEntries_hit plan ready slices input history query slice found
    exact ⟨index,inside,equal,by rw [equal]; exact actual.sizes index inside,
      by rw [equal]; exact actual.arenas index inside,by rw [equal]; exact actual.sourceLower index inside,
      by rw [equal]; exact actual.sourceBefore index inside⟩

/-- Lookup cost holds at every source clock, including insufficient funding. -/
theorem Database.body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array table : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (scratch queryPointer : BitVec 64)
    (actual : Database source array table count maximum slices scratch)
    (installed : Input.OriginalCode.Installed source.code)
    (query : Find.Key32) (view : MemoryBytes.ByteView source queryPointer query) (fits : queryPointer.toNat+32<2^64)
    (dbLocal : source.locals.lookup (ofString "db")=some (.val (.word table)))
    (hashLocal : source.locals.lookup (ofString "hash")=some (.val (.word queryPointer))) :
    source.clock-(evaluateHOLFiniteState source NodeDb.body).2.clock≤6*count+3 := by
  by_cases enough : 6*count+3≤source.clock
  · obtain ⟨answer,paid,target,price,run,frame,hit⟩ := actual.execute source array table count maximum slices scratch queryPointer installed query view fits dbLocal hashLocal enough
    have clock:=congrArg PanSemStateFiniteExact.clock frame
    change target.clock=source.clock-paid at clock
    rw [run,clock]
    omega
  · omega

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.sliceEntries_hit
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Database.execute
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Database.body_cost
