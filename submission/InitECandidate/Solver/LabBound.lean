import InitECandidate.Solver.LabBound.Assembly
import Flapjack.RiscV.CorrectnessEncoding.Complete

/-! Quantitative Lab-to-RISC-V correctness for static source code. The
multiplier includes padded ordinary instructions and terminal/FFI dispatch. -/
namespace InitECandidate.Solver.LabBound
open Flapjack Flapjack.RiscV.L3 Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target

theorem riscv {F : Type} (limit : Nat)
    (s1 s2 : LabSem.State 64 LabToTarget.Config F) (res : MachineResult)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (asm : AsmState 64) (ms : riscv_state) (pc : BitVec 64)
    (target : mc.target = riscvTarget)
    (lines : LineBound code limit) (static : NoInstall s1.code)
    (oracles : oracleTie mc ms s1) (execution : LabSem.evaluate s1 = (res, s2))
    (success : res ≠ .error) (related : stateRel (mc, code, labs, pc) s1 asm ms) :
    ∃ count post, count ≤ (16 * (limit + 1) + 2) * s1.clock ∧
      evaluateTargetHOL mc s1.ffi count ms = (res, post, s2.ffi) := by
  have bounded : EncoderBound.Contract mc.target 16 := by
    rw [target]
    exact BoundedStep.contract
  have encoder : encoderCorrect mc.target := by
    rw [target]
    exact Flapjack.RiscV.TargetProof.riscv_encoder_correct
  obtain ⟨extra, post, small, run⟩ := compileCorrectFor_all s1 res mc s2 code labs asm ms pc
    bounded lines static ⟨oracles, execution, success, encoder, related⟩
  exact ⟨s1.clock + extra, post, small, run⟩

end InitECandidate.Solver.LabBound

#print axioms InitECandidate.Solver.LabBound.riscv
