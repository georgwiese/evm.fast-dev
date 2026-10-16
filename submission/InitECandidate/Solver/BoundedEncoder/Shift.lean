import InitECandidate.Solver.BoundedEncoder.ShiftLslRegister
import InitECandidate.Solver.BoundedEncoder.ShiftLslImmediate
import InitECandidate.Solver.BoundedEncoder.ShiftLsrRegister
import InitECandidate.Solver.BoundedEncoder.ShiftLsrImmediate
import InitECandidate.Solver.BoundedEncoder.ShiftAsrRegister
import InitECandidate.Solver.BoundedEncoder.ShiftAsrImmediate
import InitECandidate.Solver.BoundedEncoder.ShiftRorRegister
import InitECandidate.Solver.BoundedEncoder.ShiftRorImmediate

namespace InitECandidate.Solver.BoundedEncoder
open Flapjack.RiscV.TargetProof Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target
set_option autoImplicit false

/-- Full original Shift constructor (source560-620), assembled over all four
operators and both Reg/Imm forms. Sole original source-step/initial relation
premise and complete existential all-environment assertions remain unchanged.
Each concrete case derives actual native Next from emitted bytes, including
zero-count Ror and legal aliases. Inherits reals_as_rational_cuts through native
state closure (SOUNDNESS item8). `CorrectnessEncoding.Complete`
assembles the full encoder correctness theorem. -/
theorem encoder_bounded_shift (op : Flapjack.Shift) (rd rs1 : Nat) (right : HolRegImm 64) (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.inst (.arith (.shift op rd rs1 right))) s2 ∧
      targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, n + 1 ≤ 16 ∧ ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.inst (.arith (.shift op rd rs1 right)))).length s1.pc
      asserts n (fun k s => env (n - k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  cases op <;> cases right
  · exact encoder_bounded_shiftLslRegister rd rs1 _ s1 s2 ms h
  · exact encoder_bounded_shiftLslImmediate rd rs1 _ s1 s2 ms h
  · exact encoder_bounded_shiftLsrRegister rd rs1 _ s1 s2 ms h
  · exact encoder_bounded_shiftLsrImmediate rd rs1 _ s1 s2 ms h
  · exact encoder_bounded_shiftAsrRegister rd rs1 _ s1 s2 ms h
  · exact encoder_bounded_shiftAsrImmediate rd rs1 _ s1 s2 ms h
  · exact encoder_bounded_shiftRorRegister rd rs1 _ s1 s2 ms h
  · exact encoder_bounded_shiftRorImmediate rd rs1 _ s1 s2 ms h

end InitECandidate.Solver.BoundedEncoder

#print axioms InitECandidate.Solver.BoundedEncoder.encoder_bounded_shift
