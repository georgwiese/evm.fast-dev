import InitECandidate.Solver.MutableTable.WitnessBuildRecords

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Real decoded record pointer/length cells survive a later constructor's
own-memory frame. This supplies the original lookup's slice cells after the
second map is built, without requiring equality of the two private maps. -/
theorem prior_records_preserved (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan) (table : Nat)
    (before : plan.table+72+57*plan.capacity+plan.padding≤table)
    (stp pad out : BitVec 64)
    (stateArena : AllocatedBytes.Arena stp 200) (paddingArena : AllocatedBytes.Arena pad 136) (outputArena : AllocatedBytes.Arena out 32)
    (buffersBefore : stp.toNat+200≤plan.records ∧ pad.toNat+136≤plan.records ∧ out.toNat+32≤plan.records)
    (frame : ∀ query,query.toNat<table ∧ Keccak256.Protected stp pad out query → target.memory query=source.memory query)
    (slices : Nat → Graph.Slice) (records : Records source plan slices) : Records target plan slices := by
  have kept (index offset : Nat) (inside : index<plan.count) (offsetInside : offset<16) :
      target.memory (recordCell plan index offset)=source.memory (recordCell plan index offset) := by
    have address:=record_number plan ready index offset inside offsetInside
    have arrayBefore:=ready.recordsBefore
    apply frame
    refine ⟨by rw [address];omega,?_,?_,?_⟩
    · exact AllocatedBytes.Arena.away_above stp _ 200 stateArena (by rw [address];have:=buffersBefore.1;omega)
    · exact AllocatedBytes.Arena.away_above pad _ 136 paddingArena (by rw [address];have:=buffersBefore.2.1;omega)
    · exact AllocatedBytes.Arena.away_above out _ 32 outputArena (by rw [address];have:=buffersBefore.2.2;omega)
  exact ⟨by intro index inside;exact (kept index 0 inside (by decide)).trans (records.pointers index inside),
    by intro index inside;exact (kept index 8 inside (by decide)).trans (records.lengths index inside)⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.prior_records_preserved
