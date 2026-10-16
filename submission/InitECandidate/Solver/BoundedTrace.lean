import InitECandidate.Solver.BoundedEncoder

/-! Uniform evaluator cost for arbitrary checked ASM traces. Unlike an exact
counter per instruction, the existential count may depend on the source state
(for example, a conditional branch's outcome). -/
namespace InitECandidate.Solver.BoundedTrace
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver InitECandidate.Solver.WeightedTrace

/-- Every checked ordinary ASM operation takes between one and sixteen target
evaluator transitions, with no restriction to the bootstrap instruction forms.
FFI/cache dispatch remains outside this ordinary-instruction trace theorem. -/
theorem evaluator {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (target : mc.target = riscvTarget)
    (identity : mc.nextInterfer = fun _ state => state)
    (code : List (HolAsm 64)) (s : AsmState 64)
    (checks : Checked code s) (guards : Guards mc code s)
    (ms : riscv_state) (io : HolFfiState σ)
    (related : targetStateRel riscvTarget s ms) :
    ∃ count post, code.length ≤ count ∧ count ≤ 16 * code.length ∧
      (∀ clock, evaluateTargetHOL mc io (count + clock) ms =
        evaluateTargetHOL mc io clock post) ∧
      targetStateRel riscvTarget (run code s) post := by
  induction code generalizing s ms with
  | nil => exact ⟨0, ms, by simp, by simp, fun _ => by simp, related⟩
  | cons i rest ih =>
    obtain ⟨n, bound, encoded⟩ := BoundedEncoder.encoder i s (after s i) ms checks.1 related
    have interference : interferenceOk mc.nextInterfer (riscvTarget.proj s.memDomain) := by
      intro index state
      rw [identity]
    obtain ⟨middle, first, middleRelated⟩ := RiscVEvaluatorCosts.from_encoder
      mc io s (after s i) ms i n target guards.1 guards.2.1 interference
      checks.1 related encoded
    simp only [shift_identity mc identity (n + 1)] at first
    obtain ⟨tailCount, post, lower, upper, tailRun, postRelated⟩ :=
      ih (after s i) checks.2 guards.2.2 middle middleRelated
    refine ⟨n + 1 + tailCount, post, ?_, ?_, ?_, postRelated⟩
    · simp only [List.length_cons]
      omega
    · simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    · intro clock
      rw [show n + 1 + tailCount + clock = (tailCount + clock) + (n + 1) by omega,
        first, tailRun]

end InitECandidate.Solver.BoundedTrace

#print axioms InitECandidate.Solver.BoundedTrace.evaluator
