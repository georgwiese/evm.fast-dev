import InitECandidate.Solver.WitnessRadix.TableCells
import InitECandidate.Solver.WitnessRadix.TableClearFrame

namespace InitECandidate.Solver.WitnessRadix.TableNew
open Flapjack PanSemStateFiniteExact BackingLayout

theorem result_before (memory : WordWrites.Memory) (be : Bool) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (offset : Nat) (before : offset < 48) (value : BitVec 64)
    (member : (cell (AllocatedLayout.layout plan) .header offset, value) ∈ beforeWrites plan) :
    resultMemory memory be plan (cell (AllocatedLayout.layout plan) .header offset) = .word value := by
  rw [resultMemory, WordWrites.write_away _ _ _ (after_away plan ready offset before)]
  rw [clear_memory_away _ _ _ ready _ (Or.inl (by rw [header_number plan ready offset (by omega)]; omega))]
  exact WordWrites.write_unique memory _ _ (before_distinct plan ready) member

theorem result_after (memory : WordWrites.Memory) (be : Bool) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (entry : BitVec 64 × BitVec 64) (member : entry ∈ afterWrites plan) :
    resultMemory memory be plan entry.1 = .word entry.2 :=
  WordWrites.write_unique _ _ entry (after_distinct plan ready) member

/-- All four pointer fields loaded by the radix helper have their actual
allocated values after the complete table constructor. -/
theorem result_header {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs = InitE.ordinaryDomain) :
    BuildEntry.Header { source with memory := resultMemory source.memory source.be plan }
      (AllocatedLayout.layout plan).table (AllocatedLayout.layout plan).keys
      (AllocatedLayout.layout plan).vals (AllocatedLayout.layout plan).primary (AllocatedLayout.layout plan).backup := by
  have mapped := AllocatedLayout.mapped source plan ready domain
  refine ⟨mapped .header 32 (by decide) (by change 32 + 8 ≤ 72; decide), ?_,
    mapped .header 40 (by decide) (by change 40 + 8 ≤ 72; decide), ?_,
    mapped .header 56 (by decide) (by change 56 + 8 ≤ 72; decide), ?_,
    mapped .header 64 (by decide) (by change 64 + 8 ≤ 72; decide), ?_⟩
  · exact result_before source.memory source.be plan ready 32 (by decide) _ (by
      simp [beforeWrites, cell, base, AllocatedLayout.layout, byteAddress])
  · exact result_before source.memory source.be plan ready 40 (by decide) _ (by
      simp [beforeWrites, cell, base, AllocatedLayout.layout, byteAddress])
  · exact result_after source.memory source.be plan ready
      (BitVec.ofNat 64 plan.table + 56#64, (AllocatedLayout.layout plan).primary) (by
      simp [afterWrites, AllocatedLayout.layout])
  · exact result_after source.memory source.be plan ready
      (BitVec.ofNat 64 plan.table + 64#64, (AllocatedLayout.layout plan).backup) (by
      simp [afterWrites, AllocatedLayout.layout])

theorem header_of_fields {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (table keys vals primary backup : BitVec 64) (memory : source.memory = target.memory)
    (domain : source.memaddrs = target.memaddrs) (header : BuildEntry.Header source table keys vals primary backup) :
    BuildEntry.Header target table keys vals primary backup := by
  rcases header with ⟨a,b,c,d,e,f,g,h⟩
  rw [domain] at a c e g
  rw [memory] at b d f h
  exact ⟨a,b,c,d,e,f,g,h⟩

theorem entered_header {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs = InitE.ordinaryDomain) :
    BuildEntry.Header (enteredState source plan)
      (AllocatedLayout.layout plan).table (AllocatedLayout.layout plan).keys
      (AllocatedLayout.layout plan).vals (AllocatedLayout.layout plan).primary (AllocatedLayout.layout plan).backup := by
  exact header_of_fields { source with memory := resultMemory source.memory source.be plan } (enteredState source plan)
    _ _ _ _ _ (entered_memory source plan).symm rfl (result_header source plan ready domain)

end InitECandidate.Solver.WitnessRadix.TableNew

#print axioms InitECandidate.Solver.WitnessRadix.TableNew.result_header
#print axioms InitECandidate.Solver.WitnessRadix.TableNew.entered_header
