import InitECandidate.Solver.BoundedEncoder
import InitECandidate.Solver.EncoderBound

/-! The complete encoder bound carried into the evaluator and the interference
search used by Lab-to-target correctness. -/
namespace InitECandidate.Solver.BoundedStep
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps
open InitECandidate.Solver

theorem contract : EncoderBound.Contract riscvTarget 16 := by
  intro s1 i s2 ms step related
  exact BoundedEncoder.encoder i s1 s2 ms step related

theorem evaluator {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (target : mc.target = riscvTarget)
    (s1 s2 : AsmState 64) (ms : riscv_state) (io : HolFfiState σ)
    (i : HolAsm 64)
    (domain : mc.progAddresses = s1.memDomain)
    (disjoint : ffiEntryPcsDisjoint mc s1 (riscvEnc i).length)
    (interference : interferenceOk mc.nextInterfer (riscvTarget.proj s1.memDomain))
    (step : asmStep riscvConfig s1 i s2)
    (related : targetStateRel riscvTarget s1 ms) :
    ∃ count post, 0 < count ∧ count ≤ 16 ∧ ∀ clock,
      evaluateTargetHOL mc io (clock + count) ms =
        evaluateTargetHOL (shiftInterfer count mc) io clock post ∧
      findNextInterference mc io (clock + count) ms =
        findNextInterference (shiftInterfer count mc) io clock post ∧
      targetStateRel mc.target s2 post ∧ count ≠ 0 := by
  obtain ⟨n, bound, cost⟩ := BoundedEncoder.encoder i s1 s2 ms step related
  have ok : targetOk mc.target := by
    rw [target]
    exact Flapjack.RiscV.TargetProof.riscv_target_ok
  have encode : mc.target.config.encode i = riscvEnc i := by rw [target]; rfl
  obtain ⟨post, run⟩ := EncoderClock.evaluator_exact mc s1 s2 ms io i n ok domain
    (by simpa only [encode] using disjoint)
    (by simpa only [target] using interference)
    (by simpa only [target, riscvTarget, riscvConfig_encode] using step)
    (by simpa only [target] using related)
    (by simpa only [target] using cost)
    (by rw [encode]; exact (Flapjack.RiscV.TargetProof.riscv_encoding i).2)
  exact ⟨n + 1, post, by omega, bound, run⟩

end InitECandidate.Solver.BoundedStep

#print axioms InitECandidate.Solver.BoundedStep.evaluator
#print axioms InitECandidate.Solver.BoundedStep.contract
