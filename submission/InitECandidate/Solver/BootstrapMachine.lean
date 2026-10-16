import InitE.SubmissionModel
import InitECandidate.Proofs.BootstrapMemory

/-! Connect the bootstrap ASM memory model to the challenge's actual initial
state, including arbitrary public input bytes. Only ordinary memory belongs to
the ASM relation; shared bytes remain in the concrete machine and FFI state. -/
namespace InitECandidate.Solver.BootstrapMachine
open InitE Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget

/-- Public input does not change any byte observed by the bootstrap ASM model. -/
theorem initial_related (sub : Submission) (code : sub.code = InitECandidate.code)
    (input : Guest.InputBlob) :
    targetStateRel riscvTarget initialAsm (sub.initialState input) := by
  refine ⟨sub.initialState_ok input, rfl, ?_, ?_, ?_⟩
  · intro address member
    have ordinary : ¬ submissionSharedDomain address := member.1.2
    change sub.initialMemory input address = initialMemory address
    simp only [Submission.initialMemory, if_neg ordinary, code, initialMemory]
  · intro i guard
    rfl
  · intro i guard
    have impossible : i < 0 := guard
    omega

/-- Startup uses the baseline's ordinary memory domain whenever these two
small metadata fields agree; no compiler artifact equality is required. -/
theorem program_domain (sub : Submission)
    (anchor : sub.anchorPc = nativePc) (first : sub.first = 20) :
    sub.machineConfig.progAddresses = bootstrapDomain := by
  funext address
  simp only [Submission.machineConfig, challengeMachineConfig, Submission.programDomain,
    anchor, first, bootstrapDomain, submissionMemoryDomain, memoryDomain,
    submissionSharedDomain, machineSharedDomain, ffiOffset]

/-- All foreign-call entries lie beyond the bootstrap. The only arithmetic
condition on MMIO offsets is absence of U64 address wraparound. -/
theorem ffi_above (sub : Submission)
    (anchor : sub.anchorPc = nativePc) (first : sub.first = 20)
    (offsets : ∀ rec ∈ sub.extra, nativePc + rec.entryPc < 2 ^ 64) :
    ∀ pc ∈ sub.machineConfig.ffiEntryPcs, initialPc + 208 ≤ pc.toNat := by
  intro pc member
  change pc ∈ ((List.range sub.first).map (fun i =>
    BitVec.ofNat 64 sub.anchorPc - BitVec.ofNat 64 ((3+i)*ffiOffset))) ++
      (sub.extra.map (fun rec => BitVec.ofNat 64 sub.anchorPc + BitVec.ofNat 64 rec.entryPc)) at member
  rw [anchor, first] at member
  rcases List.mem_append.mp member with ordinary | mmio
  · obtain ⟨i, bound, rfl⟩ := List.mem_map.mp ordinary
    have bound : i < 20 := List.mem_range.mp bound
    have offset : (BitVec.ofNat 64 ((3+i)*ffiOffset)).toNat = (3+i)*16 := by
      simp only [ffiOffset, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have base : (BitVec.ofNat 64 nativePc).toNat = 0x80001190 := by decide
    rw [BitVec.toNat_sub_of_le (by
      apply BitVec.le_def.mpr
      rw [offset, base]
      omega), base, offset]
    norm_num [initialPc]
    omega
  · obtain ⟨rec, recMember, rfl⟩ := List.mem_map.mp mmio
    have nowrap := offsets rec recMember
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt nowrap]
    norm_num [initialPc, nativePc]
    omega

end InitECandidate.Solver.BootstrapMachine

#print axioms InitECandidate.Solver.BootstrapMachine.initial_related
#print axioms InitECandidate.Solver.BootstrapMachine.program_domain
#print axioms InitECandidate.Solver.BootstrapMachine.ffi_above
