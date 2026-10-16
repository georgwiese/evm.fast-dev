import InitECandidate.Solver.SupportedCosts
import InitECandidate.Solver.BootstrapEncoding

/-! Quantitative bootstrap trace, using the checked literal byte encoding.
Initial-state ASM checks and evaluator guards remain explicit obligations. -/
namespace InitECandidate.Solver.BootstrapCost
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.SupportedCosts
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem block_supported : ∀ i ∈ bootstrapBlocks.map Prod.snd, Supported i := by
  intro i member
  simp only [bootstrapBlocks, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact .loc _ _
    | exact .const _ _
    | exact .lsl _ _ _
    | exact .memory _ _ _ _
    | exact .binop _ _ _ _
    | exact .jump _ (by decide)
    | exact .jumpCmp _ _ _ _ (by decide) (by decide)

private theorem part_supported (part : List (Nat × HolAsm 64))
    (subset : ∀ b ∈ part, b ∈ bootstrapBlocks) :
    ∀ i ∈ part.map Prod.snd, Supported i := by
  intro i member
  obtain ⟨b, member, eq⟩ := List.mem_map.mp member
  exact block_supported i (List.mem_map.mpr ⟨b, subset b member, eq⟩)

theorem trace_supported : ∀ i ∈ trace, Supported i := by
  have pre : ∀ i ∈ prelude, Supported i :=
    part_supported _ (fun _ h => List.mem_of_mem_take h)
  have mid : ∀ i ∈ body, Supported i :=
    part_supported _ (fun _ h => List.mem_of_mem_drop (List.mem_of_mem_take h))
  have last : ∀ i ∈ tail, Supported i :=
    part_supported _ (fun _ h => List.mem_of_mem_drop h)
  intro i member
  simp only [trace, List.mem_append] at member
  rcases member with (member | member) | member
  · exact pre i member
  · obtain ⟨row, rowMember, member⟩ := List.mem_flatten.mp member
    have eq := (List.mem_replicate.mp rowMember).2
    subst row
    exact mid i member
  · exact last i member

private theorem total_append (a b : List (HolAsm 64)) :
    WeightedTrace.total counter (a ++ b) =
      WeightedTrace.total counter a + WeightedTrace.total counter b := by
  simp [WeightedTrace.total]

private theorem total_replicate (n : Nat) :
    WeightedTrace.total counter (List.replicate n body).flatten =
      n * WeightedTrace.total counter body := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons, total_append, ih, Nat.succ_mul]
    omega

theorem exact_total : WeightedTrace.total counter trace = 23132 := by
  have pre : WeightedTrace.total counter prelude = 6 := by decide
  have mid : WeightedTrace.total counter body = 5 := by decide
  have last : WeightedTrace.total counter tail = 41 := by decide
  rw [trace, total_append, total_append, total_replicate, pre, mid, last]

/-- The concrete trace has exactly the measured 23,132 formal prefix steps,
provided the original ASM checks and evaluator guards are discharged. The
initial-state checks and identification of the endpoint remain separate tasks. -/
theorem evaluator {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (target : mc.target = riscvTarget)
    (identity : mc.nextInterfer = fun _ state => state)
    (s : AsmState 64) (ms : riscv_state) (io : HolFfiState σ)
    (checks : WeightedTrace.Checked trace s)
    (guards : WeightedTrace.Guards mc trace s)
    (related : targetStateRel riscvTarget s ms) :
    ∃ post,
      (∀ clock, evaluateTargetHOL mc io (23132 + clock) ms =
        evaluateTargetHOL mc io clock post) ∧
      targetStateRel riscvTarget (WeightedTrace.run trace s) post := by
  simpa only [exact_total] using WeightedTrace.evaluator mc target identity counter trace
    (trace_costs trace trace_supported) s checks guards ms io related

end InitECandidate.Solver.BootstrapCost

#print axioms InitECandidate.Solver.BootstrapCost.bytes_match
#print axioms InitECandidate.Solver.BootstrapCost.exact_total
#print axioms InitECandidate.Solver.BootstrapCost.evaluator
