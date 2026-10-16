import InitECandidate.Solver.BootstrapTailChecks
import InitECandidate.Solver.BootstrapMachine

/-! A quantified startup bound for the actual challenge initial state. All ASM
execution and dispatch obligations are discharged; only the submission's code
and small configuration fields are parameters. -/
namespace InitECandidate.Solver.BootstrapStartup
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open InitE InitECandidate.Solver BootstrapChecks

theorem checked : WeightedTrace.Checked BootstrapCost.trace initialAsm := by
  rw [BootstrapCost.trace, checked_append, checked_append, run_append, prelude_endpoint,
    copy_endpoint]
  exact ⟨⟨prelude_checked, copy_checked⟩,
    (checked_iff _ _).mpr (by
      rw [tail_eq]
      exact BootstrapTailChecks.tail_checked)⟩

theorem region : BootstrapRegion.Within bootstrapDomain initialPc (initialPc + 208)
    BootstrapCost.trace initialAsm := by
  rw [BootstrapCost.trace, BootstrapRegion.append, BootstrapRegion.append,
    run_append, prelude_endpoint, copy_endpoint]
  exact ⟨⟨prelude_region, copy_region⟩, by
    rw [tail_eq]
    exact BootstrapTailChecks.tail_guards⟩

theorem endpoint : WeightedTrace.run BootstrapCost.trace initialAsm = installedAsm := by
  rw [BootstrapCost.trace, run_append, run_append, prelude_endpoint, copy_endpoint,
    run_eq, tail_eq]
  exact InitECandidate.Proofs.BootstrapStraightLine.tail_endpoint_eq
    BootstrapTailChecks.tail_checked

/-- The real startup consumes exactly 23,132 evaluator transitions for every
input. The equality holds for every remaining clock, so this theorem composes
with any subsequently established guest bound. -/
theorem evaluator {σ : Type} (sub : Submission)
    (code : sub.code = InitECandidate.code)
    (anchor : sub.anchorPc = nativePc) (first : sub.first = 20)
    (offsets : ∀ rec ∈ sub.extra, nativePc + rec.entryPc < 2 ^ 64)
    (input : Guest.InputBlob) (io : HolFfiState σ) :
    ∃ post,
      (∀ clock, evaluateTargetHOL sub.machineConfig io (23132 + clock)
        (sub.initialState input) = evaluateTargetHOL sub.machineConfig io clock post) ∧
      targetStateRel riscvTarget installedAsm post := by
  have guards := BootstrapRegion.guards sub.machineConfig bootstrapDomain initialPc
    (initialPc + 208) (BootstrapMachine.program_domain sub anchor first) (by decide)
    (BootstrapMachine.ffi_above sub anchor first offsets) _ _ region
  simpa only [endpoint] using BootstrapCost.evaluator sub.machineConfig rfl rfl
    initialAsm (sub.initialState input) io checked guards
    (BootstrapMachine.initial_related sub code input)

end InitECandidate.Solver.BootstrapStartup

#print axioms InitECandidate.Solver.BootstrapStartup.checked
#print axioms InitECandidate.Solver.BootstrapStartup.region
#print axioms InitECandidate.Solver.BootstrapStartup.endpoint
#print axioms InitECandidate.Solver.BootstrapStartup.evaluator
