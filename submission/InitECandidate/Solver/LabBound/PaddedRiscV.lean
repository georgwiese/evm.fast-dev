import InitECandidate.Solver.LabBound.StaticTarget
import InitECandidate.Solver.LabBound.PaddedProgram

/-! Quantitative execution for the actual fixed padded section declarations.
The original initial-state relation and Lab execution still need to be supplied;
this theorem discharges only the extra layout/static-code premises. -/
namespace InitECandidate.Solver.LabBound
open Flapjack Flapjack.RiscV.L3 Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target

theorem padded_riscv {F : Type}
    (s1 s2 : LabSem.State 64 LabToTarget.Config F) (res : MachineResult)
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (labs : Spt (Spt Nat)) (asm : AsmState 64) (ms : riscv_state) (pc : BitVec 64)
    (target : mc.target = riscvTarget)
    (oracles : oracleTie mc ms s1) (execution : LabSem.evaluate s1 = (res, s2))
    (success : res ≠ .error)
    (related : stateRel (mc, fixedPaddedProgram, labs, pc) s1 asm ms) :
    ∃ count post, count ≤ 402 * s1.clock ∧
      evaluateTargetHOL mc s1.ffi count ms = (res, post, s2.ffi) :=
  riscv_static_target 24 s1 s2 res mc fixedPaddedProgram labs asm ms pc target
    fixedPaddedProgram_layout oracles execution success related

end InitECandidate.Solver.LabBound
#print axioms InitECandidate.Solver.LabBound.padded_riscv
