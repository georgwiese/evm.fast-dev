import InitECandidate.Solver.WeightedTrace
import InitECandidate.Solver.ConstCost
import InitECandidate.Solver.BinopRegisterCost
import InitECandidate.Solver.BinopImmediateCost
import InitECandidate.Solver.ShiftLslImmediateCost
import InitECandidate.Solver.JumpNearCost
import InitECandidate.Solver.JumpCmpNearCost

/-! Exact encoder counters for a useful, explicitly restricted ASM subset.
This covers the bootstrap instruction forms. It is not yet the full compiler's
instruction set; unsupported forms are never admitted by Supported. -/
namespace InitECandidate.Solver.SupportedCosts
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver.EncoderClock

inductive Supported : HolAsm 64 → Prop where
  | skip : Supported (.inst .skip)
  | const (r : Nat) (c : BitVec 64) : Supported (.inst (.const r c))
  | binop (op : HolBinop) (rd rs : Nat) (right : HolRegImm 64) :
      Supported (.inst (.arith (.binop op rd rs right)))
  | lsl (rd rs : Nat) (c : BitVec 64) : Supported (.inst (.arith (.shift .lsl rd rs (.imm c))))
  | memory (m : HolMemop) (r base : Nat) (w : BitVec 64) : Supported (.inst (.mem m r (.addr base w)))
  | loc (r : Nat) (c : BitVec 64) : Supported (.loc r c)
  | jump (c : BitVec 64) (range : -1048576 ≤ c.toInt ∧ c.toInt ≤ 1048575) : Supported (.jump c)
  | jumpCmp (cmp : Cmp) (r1 r2 : Nat) (c : BitVec 64)
      (range : -4092 ≤ c.toInt ∧ c.toInt ≤ 4095)
      (simple : cmp ≠ .test ∧ cmp ≠ .notTest) : Supported (.jumpCmp cmp r1 (.reg r2) c)

/-- The assertion counter is one less than the native transition count. Values
on unsupported instructions have no semantic guarantee. -/
def counter : HolAsm 64 → Nat
  | .loc _ _ => 1
  | .inst (.const r c) => (riscvAst (.inst (.const r c))).length - 1
  | _ => 0

theorem encoder (i : HolAsm 64) (supported : Supported i)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (step : asmStep riscvConfig s1 i s2)
    (related : targetStateRel riscvTarget s1 ms) :
    EncoderAt riscvTarget s1 s2 ms i (counter i) := by
  cases supported with
  | skip => exact SkipCost.skip_encoder_exact s1 s2 ms ⟨step, related⟩
  | const r c => exact ConstCost.encoder_exact r c s1 s2 ms ⟨step, related⟩
  | binop op rd rs right =>
    cases right with
    | reg r => exact BinopRegisterCost.encoder_exact op rd rs r s1 s2 ms ⟨step, related⟩
    | imm c => exact BinopImmediateCost.encoder_exact op rd rs c s1 s2 ms ⟨step, related⟩
  | lsl rd rs c => exact ShiftLslImmediateCost.encoder_exact rd rs c s1 s2 ms ⟨step, related⟩
  | memory m r base w => exact MemoryCost.memory_encoder_exact m r base w s1 s2 ms ⟨step, related⟩
  | loc r c => exact LocCost.loc_encoder_exact r c s1 s2 ms ⟨step, related⟩
  | jump c range => exact JumpNearCost.encoder_exact c s1 s2 ms ⟨step, related⟩ range
  | jumpCmp cmp r1 r2 c range simple =>
    exact JumpCmpNearCost.encoder_exact cmp r1 r2 c s1 s2 ms ⟨step, related⟩ range simple

theorem cost_le_six (i : HolAsm 64) (supported : Supported i) : counter i + 1 ≤ 6 := by
  cases supported with
  | const r c =>
    have upper := ConstCost.length_le_six r c
    change (riscvAst (.inst (.const r c))).length - 1 + 1 ≤ 6
    omega
  | binop op rd rs right => cases right <;> simp [counter]
  | skip | lsl | memory | loc | jump | jumpCmp => simp [counter]

theorem trace_costs (code : List (HolAsm 64))
    (supported : ∀ i ∈ code, Supported i) : WeightedTrace.Costs counter code :=
  fun i member s1 s2 ms step related => encoder i (supported i member) s1 s2 ms step related

theorem trace_bound (code : List (HolAsm 64))
    (supported : ∀ i ∈ code, Supported i) : WeightedTrace.total counter code ≤ 6 * code.length :=
  WeightedTrace.total_le counter code 6 (fun i member => cost_le_six i (supported i member))

end InitECandidate.Solver.SupportedCosts

#print axioms InitECandidate.Solver.SupportedCosts.encoder
#print axioms InitECandidate.Solver.SupportedCosts.cost_le_six
#print axioms InitECandidate.Solver.SupportedCosts.trace_bound
