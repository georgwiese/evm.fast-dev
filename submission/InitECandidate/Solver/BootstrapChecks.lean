import InitECandidate.Proofs.BootstrapStraightLine
import InitECandidate.Proofs.BootstrapCopyTrace
import InitECandidate.Solver.BootstrapCost
import InitECandidate.Solver.BootstrapRegion

/-! Reuse the fixed bootstrap's actual ASM proofs without importing its large
ArtifactFacts/configuration closure. The old and quantitative trace predicates
are linked structurally, so no target execution is assumed. -/
namespace InitECandidate.Solver.BootstrapChecks
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open InitECandidate.Solver

/-- Both developments use the same pinned ASM update. -/
theorem after_eq (s : AsmState 64) (i : HolAsm 64) :
    WeightedTrace.after s i = InitECandidate.Proofs.BootstrapSteps.after s i := rfl

theorem run_eq (code : List (HolAsm 64)) (s : AsmState 64) :
    WeightedTrace.run code s = InitECandidate.Proofs.BootstrapCopy.run code s := by
  induction code generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change WeightedTrace.run rest (WeightedTrace.after s i) =
      InitECandidate.Proofs.BootstrapCopy.run rest (InitECandidate.Proofs.BootstrapSteps.after s i)
    exact ih _

theorem checked_iff (code : List (HolAsm 64)) (s : AsmState 64) :
    WeightedTrace.Checked code s ↔ InitECandidate.Proofs.BootstrapCopy.Checked code s := by
  induction code generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [WeightedTrace.Checked, InitECandidate.Proofs.BootstrapCopy.Checked,
      after_eq, ih]

theorem prelude_eq : BootstrapCost.prelude =
    InitECandidate.Proofs.BootstrapStraightLine.prefixCode := rfl

theorem body_eq : BootstrapCost.body = InitECandidate.Proofs.BootstrapCopy.loopBody := rfl

theorem tail_eq : BootstrapCost.tail =
    InitECandidate.Proofs.BootstrapStraightLine.tailCode := rfl

/-- Actual installed code, alignment and source-state checks for all three
address loads at startup. No native run is a hypothesis. -/
theorem prelude_checked : WeightedTrace.Checked BootstrapCost.prelude InitE.initialAsm := by
  rw [checked_iff, prelude_eq]
  exact InitECandidate.Proofs.BootstrapStraightLine.prefix_checked

/-- Actual installed code, memory and state checks for all 4,617 loop iterations. -/
theorem copy_checked : WeightedTrace.Checked
    (List.replicate 4617 BootstrapCost.body).flatten InitE.copyEntryAsm := by
  rw [checked_iff, body_eq]
  exact InitECandidate.Proofs.BootstrapCopy.copyLoop_checked

theorem prelude_endpoint : WeightedTrace.run BootstrapCost.prelude InitE.initialAsm =
    InitE.copyEntryAsm := by
  rw [run_eq, prelude_eq]
  exact InitECandidate.Proofs.BootstrapStraightLine.prefix_endpoint

theorem copy_endpoint : WeightedTrace.run
    (List.replicate 4617 BootstrapCost.body).flatten InitE.copyEntryAsm =
      InitECandidate.Proofs.BootstrapCopy.copyState 4617 := by
  rw [run_eq, body_eq]
  exact InitECandidate.Proofs.BootstrapCopy.loopProgram_run 4617 InitE.copyEntryAsm


/-- Structural append rules keep the 23,120-operation trace symbolic. -/
theorem run_append (left right : List (HolAsm 64)) (s : AsmState 64) :
    WeightedTrace.run (left ++ right) s =
      WeightedTrace.run right (WeightedTrace.run left s) := by
  induction left generalizing s with
  | nil => rfl
  | cons i rest ih => exact ih _

theorem checked_append (left right : List (HolAsm 64)) (s : AsmState 64) :
    WeightedTrace.Checked (left ++ right) s ↔
      WeightedTrace.Checked left s ∧ WeightedTrace.Checked right (WeightedTrace.run left s) := by
  induction left generalizing s with
  | nil => simp [WeightedTrace.Checked, WeightedTrace.run]
  | cons i rest ih => simp only [List.cons_append, WeightedTrace.Checked, WeightedTrace.run, ih, and_assoc]

open InitE Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Proofs.BootstrapCopy InitECandidate.Proofs.BootstrapStraightLine

/-- Closed code-range facts for the three initial address loads. -/
theorem prelude_region : BootstrapRegion.Within bootstrapDomain initialPc (initialPc + 208)
    BootstrapCost.prelude initialAsm := by
  rw [prelude_eq]
  simp only [prefixCode, bootstrapBlocks, List.take, List.map, BootstrapRegion.Within]
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_, rfl, ?_, ?_, trivial⟩
  all_goals decide

private theorem loop_instruction_length (stage : Nat) (hs : stage < 5) :
    (riscvEnc loopBody[stage]).length = 4 := by interval_cases stage <;> decide +revert

private theorem body_region_step (k stage : Nat) (hk : k < 4617) (hs : stage < 5) :
    (bodyState (copyState k) stage).memDomain = bootstrapDomain ∧
    initialPc ≤ (bodyState (copyState k) stage).pc.toNat ∧
    (bodyState (copyState k) stage).pc.toNat + (riscvEnc loopBody[stage]).length ≤ initialPc + 208 := by
  refine ⟨(bodyState_config _ _ (by omega)).2.1.trans (copyState_fields k).2.1, ?_, ?_⟩
  · rw [bodyState_pc _ _ hs, copyState_pc k (by omega)]
    simp only [hk, reduceIte]
    change initialPc ≤ (BitVec.ofNat 64 0x80000018 + BitVec.ofNat 64 (4 * stage)).toNat
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    norm_num [initialPc]
    omega
  · rw [loop_instruction_length stage hs, bodyState_pc _ _ hs, copyState_pc k (by omega)]
    simp only [hk, reduceIte]
    change (BitVec.ofNat 64 0x80000018 + BitVec.ofNat 64 (4 * stage)).toNat + 4 ≤ initialPc + 208
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    norm_num [initialPc]
    omega

theorem copy_body_region (k : Nat) (hk : k < 4617) :
    BootstrapRegion.Within bootstrapDomain initialPc (initialPc + 208) loopBody (copyState k) := by
  have h0 := body_region_step k 0 hk (by decide)
  have h1 := body_region_step k 1 hk (by decide)
  have h2 := body_region_step k 2 hk (by decide)
  have h3 := body_region_step k 3 hk (by decide)
  have h4 := body_region_step k 4 hk (by decide)
  simpa [BootstrapRegion.Within, loopBody, bodyState, InitECandidate.Proofs.BootstrapCopy.run,
    after_eq, and_assoc] using
    And.intro h0 (And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4 True.intro))))


theorem copy_region_from (count start : Nat) (bound : start + count ≤ 4617) :
    BootstrapRegion.Within bootstrapDomain initialPc (initialPc + 208)
      (loopProgram count) (copyState start) := by
  induction count generalizing start with
  | zero => trivial
  | succ count ih =>
    have program : loopProgram (count + 1) = loopBody ++ loopProgram count := by
      simp [loopProgram, List.replicate_succ]
    rw [program, BootstrapRegion.append]
    refine ⟨copy_body_region start (by omega), ?_⟩
    rw [run_eq]
    have next : InitECandidate.Proofs.BootstrapCopy.run loopBody (copyState start) =
        copyState (start + 1) := by simp only [copyState, Function.iterate_succ_apply']
    rw [next]
    exact ih (start + 1) (by omega)

theorem copy_region : BootstrapRegion.Within bootstrapDomain initialPc (initialPc + 208)
    (List.replicate 4617 BootstrapCost.body).flatten copyEntryAsm := by
  rw [body_eq]
  exact copy_region_from 4617 0 (by decide)

end InitECandidate.Solver.BootstrapChecks

#print axioms InitECandidate.Solver.BootstrapChecks.prelude_checked
#print axioms InitECandidate.Solver.BootstrapChecks.copy_checked
#print axioms InitECandidate.Solver.BootstrapChecks.copy_endpoint

#print axioms InitECandidate.Solver.BootstrapChecks.prelude_region
#print axioms InitECandidate.Solver.BootstrapChecks.copy_region
