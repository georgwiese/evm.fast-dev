import InitECandidate.Solver.Input.CurrentHash.FixedRecordProgram
import InitECandidate.Solver.Input.CopyAwaySubrange

namespace InitECandidate.Solver.Input.CurrentHash.FixedRecord
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem steps_input_bounds (kind : Kind) : ∀ step ∈ kind.steps, step.inputOffset+step.length≤kind.length := by
  cases kind <;> simp [Kind.steps,Step.inputOffset,Step.length,Kind.length]

theorem steps_field_bounds (kind : Kind) : ∀ step ∈ kind.steps, step.field<kind.count := by
  cases kind <;> simp [Kind.steps,Step.field,Kind.count]

/-- Actual record/input and allocated chunk extents supply all field arenas;
no additional room is reserved for nested temporary hash allocations. -/
theorem steps_geometry (kind : Kind) (p ch query : BitVec 64)
    (inputArena : AllocatedBytes.Arena p kind.length) (chunksArena : AllocatedBytes.Arena ch (32*kind.count))
    (aligned : ch.toNat%8=0) (below : query.toNat<ch.toNat) :
    ∀ step ∈ kind.steps, AllocatedBytes.Arena (p+BitVec.ofNat 64 step.inputOffset) step.length ∧
      AllocatedBytes.Arena (ch+BitVec.ofNat 64 (32*step.field)) 32 ∧
      (ch+BitVec.ofNat 64 (32*step.field)).toNat%8=0 ∧ CopyGeneral.Away (ch+BitVec.ofNat 64 (32*step.field)) query 32 := by
  intro step member
  have inside := steps_field_bounds kind step member
  have input := AllocatedBytes.Arena.subrange p kind.length step.inputOffset step.length inputArena (steps_input_bounds kind step member)
  have output := AllocatedBytes.Arena.subrange ch (32*kind.count) (32*step.field) 32 chunksArena (by omega)
  have noWrap : ch.toNat+32*step.field<2^64 := by have h:=chunksArena.upper; omega
  have outputAligned := byteAddress_aligned ch (32*step.field) aligned (by omega) noWrap
  refine ⟨input,output,outputAligned,?_⟩
  apply CopyGeneral.Away.after _ query 32 outputAligned (by have h:=output.upper; omega)
  change query.toNat<(byteAddress ch (32*step.field)).toNat
  rw [byteAddress_toNat ch (32*step.field) noWrap]
  omega

end InitECandidate.Solver.Input.CurrentHash.FixedRecord

#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.steps_input_bounds
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.steps_field_bounds
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.steps_geometry
