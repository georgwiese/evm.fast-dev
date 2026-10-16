import InitECandidate.Solver.RiscVEvaluatorCosts

/-! Quantitative trace composition independent of the large baseline proof
library. The ASM updates, step checks and evaluator guards use the pinned
semantics. Costs are explicit local proof obligations, not inferred from code
length. The fixed challenge's nextInterfer is identity. -/
namespace InitECandidate.Solver.WeightedTrace
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps
open InitECandidate.Solver.EncoderClock InitECandidate.Solver.RiscVEvaluatorCosts

noncomputable def after (s : AsmState 64) (i : HolAsm 64) : AsmState 64 :=
  asmUpd i (s.pc + BitVec.ofNat 64 (riscvEnc i).length) s

noncomputable def run : List (HolAsm 64) → AsmState 64 → AsmState 64
  | [], s => s
  | i :: rest, s => run rest (after s i)

noncomputable def Checked : List (HolAsm 64) → AsmState 64 → Prop
  | [], _ => True
  | i :: rest, s => asmStep riscvConfig s i (after s i) ∧ Checked rest (after s i)

noncomputable def Guards (mc : MachineConfig 64 riscv_state RiscVProjection) :
    List (HolAsm 64) → AsmState 64 → Prop
  | [], _ => True
  | i :: rest, s => mc.progAddresses = s.memDomain ∧
      ffiEntryPcsDisjoint mc s (riscvEnc i).length ∧ Guards mc rest (after s i)

/-- This proof obligation is per instruction, for every related machine state.
Using the counter n gives an exact cost n+1 without truncated subtraction. -/
def Costs (counter : HolAsm 64 → Nat) (code : List (HolAsm 64)) : Prop :=
  ∀ i ∈ code, ∀ s1 s2 ms,
    asmStep riscvConfig s1 i s2 → targetStateRel riscvTarget s1 ms →
    EncoderAt riscvTarget s1 s2 ms i (counter i)

def total (counter : HolAsm 64 → Nat) (code : List (HolAsm 64)) : Nat :=
  (code.map (fun i => counter i + 1)).sum

theorem shift_identity (mc : MachineConfig 64 riscv_state RiscVProjection)
    (identity : mc.nextInterfer = fun _ state => state) (count : Nat) :
    shiftInterfer count mc = mc := by
  have shifted : holShiftSeq count mc.nextInterfer = mc.nextInterfer := by
    rw [identity]
    rfl
  simp only [shiftInterfer, shifted]

/-- The sum of exact local costs is an exact evaluateTargetHOL prefix. This
preserves the endpoint relation and every possible tail clock and FFI state. -/
theorem evaluator {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (target : mc.target = riscvTarget)
    (identity : mc.nextInterfer = fun _ state => state)
    (counter : HolAsm 64 → Nat) (code : List (HolAsm 64))
    (costs : Costs counter code) (s : AsmState 64)
    (checks : Checked code s) (guards : Guards mc code s)
    (ms : riscv_state) (io : HolFfiState σ)
    (related : targetStateRel riscvTarget s ms) :
    ∃ post,
      (∀ clock, evaluateTargetHOL mc io (total counter code + clock) ms =
        evaluateTargetHOL mc io clock post) ∧
      targetStateRel riscvTarget (run code s) post := by
  induction code generalizing s ms with
  | nil => exact ⟨ms, fun _ => by simp [total], related⟩
  | cons i rest ih =>
    have interference : interferenceOk mc.nextInterfer (riscvTarget.proj s.memDomain) := by
      intro index state
      rw [identity]
    obtain ⟨middle, first, middleRelated⟩ := from_encoder mc io s (after s i) ms i
      (counter i) target guards.1 guards.2.1 interference checks.1 related
      (costs i (by simp) s (after s i) ms checks.1 related)
    have shiftEq := shift_identity mc identity (counter i + 1)
    simp only [shiftEq] at first
    have tailCosts : Costs counter rest :=
      fun j member => costs j (List.mem_cons_of_mem i member)
    obtain ⟨post, restRun, postRelated⟩ :=
      ih tailCosts (after s i) checks.2 guards.2.2 middle middleRelated
    refine ⟨post, ?_, postRelated⟩
    intro clock
    change evaluateTargetHOL mc io ((counter i + 1 + total counter rest) + clock) ms = _
    rw [show (counter i + 1 + total counter rest) + clock =
      (total counter rest + clock) + (counter i + 1) by omega, first, restRun]

/-- Uniform encoder ceilings compose with the actual ASM trace length. -/
theorem total_le (counter : HolAsm 64 → Nat) (code : List (HolAsm 64)) (perStep : Nat)
    (bounded : ∀ i ∈ code, counter i + 1 ≤ perStep) :
    total counter code ≤ perStep * code.length := by
  induction code with
  | nil => simp [total]
  | cons i rest ih =>
    have head := bounded i (by simp)
    have tail := ih (fun j member => bounded j (List.mem_cons_of_mem i member))
    simp only [total, List.map_cons, List.sum_cons, List.length_cons] at *
    calc
      counter i + 1 + (List.map (fun j => counter j + 1) rest).sum ≤
          perStep + perStep * rest.length := Nat.add_le_add head tail
      _ = perStep * (rest.length + 1) := by simp [Nat.mul_add, Nat.add_comm]

end InitECandidate.Solver.WeightedTrace

#print axioms InitECandidate.Solver.WeightedTrace.evaluator
#print axioms InitECandidate.Solver.WeightedTrace.total_le
