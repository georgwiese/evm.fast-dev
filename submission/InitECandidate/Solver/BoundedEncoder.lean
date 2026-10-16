import InitECandidate.Solver.SupportedCosts
import InitECandidate.Solver.BoundedEncoder.Shift
import InitECandidate.Solver.BoundedEncoder.Div
import InitECandidate.Solver.BoundedEncoder.LongMul
import InitECandidate.Solver.BoundedEncoder.Rejected
import InitECandidate.Solver.BoundedEncoder.AddCarry
import InitECandidate.Solver.BoundedEncoder.AddOverflow
import InitECandidate.Solver.BoundedEncoder.SubOverflow
import InitECandidate.Solver.BoundedEncoder.Jump
import InitECandidate.Solver.BoundedEncoder.JumpCmp
import InitECandidate.Solver.BoundedEncoder.Call
import InitECandidate.Solver.BoundedEncoder.JumpReg

/-! A uniform native transition bound for every RISC-V ASM constructor.
The bound is deliberately loose. It retains both original assertion predicates
and every interference environment; no successful target execution is assumed.
It does not bound the number of source ASM operations in a guest execution. -/
namespace InitECandidate.Solver.BoundedEncoder
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Solver

private theorem supported (i : HolAsm 64) (support : SupportedCosts.Supported i)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvConfig s1 i s2 ∧ targetStateRel riscvTarget s1 ms) :
    ∃ n, n + 1 ≤ 16 ∧ EncoderClock.EncoderAt riscvTarget s1 s2 ms i n := by
  refine ⟨SupportedCosts.counter i, ?_, SupportedCosts.encoder i support s1 s2 ms h.1 h.2⟩
  have bound := SupportedCosts.cost_le_six i support
  omega

theorem encoder (i : HolAsm 64) (s1 s2 : AsmState 64) (ms : riscv_state)
    (step : asmStep riscvConfig s1 i s2)
    (related : targetStateRel riscvTarget s1 ms) :
    ∃ n, n + 1 ≤ 16 ∧ EncoderClock.EncoderAt riscvTarget s1 s2 ms i n := by
  have h := And.intro step related
  cases i with
  | inst value =>
    cases value with
    | skip => exact supported _ .skip s1 s2 ms h
    | const r c => exact supported _ (.const r c) s1 s2 ms h
    | arith a =>
      cases a with
      | binop op r t right => exact supported _ (.binop op r t right) s1 s2 ms h
      | shift op r t right => exact encoder_bounded_shift op r t right s1 s2 ms h
      | div r t u => exact encoder_bounded_div r t u s1 s2 ms h
      | longMul r t u v => exact encoder_bounded_longmul r t u v s1 s2 ms h
      | longDiv r t u v q => exact encoder_bounded_longdiv r t u v q s1 s2 ms h
      | addCarry r t u v => exact encoder_bounded_addcarry r t u v s1 s2 ms h
      | addOverflow r t u v => exact encoder_bounded_addoverflow r t u v s1 s2 ms h
      | subOverflow r t u v => exact encoder_bounded_suboverflow r t u v s1 s2 ms h
    | mem m r address =>
      cases address with
      | addr base w => exact supported _ (.memory m r base w) s1 s2 ms h
  | jump c => exact encoder_bounded_jump c s1 s2 ms h
  | jumpCmp c r right a => exact encoder_bounded_jumpCmp c r right a s1 s2 ms h
  | call c => exact encoder_bounded_call c s1 s2 ms h
  | jumpReg r => exact encoder_bounded_jumpReg r s1 s2 ms h
  | loc r c => exact supported _ (.loc r c) s1 s2 ms h

end InitECandidate.Solver.BoundedEncoder

#print axioms InitECandidate.Solver.BoundedEncoder.encoder
