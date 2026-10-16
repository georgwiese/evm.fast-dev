import InitECandidate.Solver.LabBoundTight
import InitECandidate.Solver.LabBound.StaticTarget
import Mathlib.Tactic.Tauto

/-! The full compiler relation transfers installation absence from target code
to source code, so callers need only certify the target program's syntax. -/
namespace InitECandidate.Solver.LabBoundTight
open Flapjack Flapjack.RiscV.L3 Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target

theorem riscv_static_target {F : Type} (limit : Nat)
    (s1 s2 : LabSem.State 64 LabToTarget.Config F) (res : MachineResult)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (asm : AsmState 64) (ms : riscv_state) (pc : BitVec 64)
    (target : mc.target = riscvTarget)
    (layout : LineBound code limit ∧ NoInstall code)
    (oracles : oracleTie mc ms s1) (execution : LabSem.evaluate s1 = (res, s2))
    (success : res ≠ .error) (related : stateRel (mc, code, labs, pc) s1 asm ms) :
    ∃ count post, count ≤ (16 + limit / 4 + 2) * s1.clock ∧
      evaluateTargetHOL mc s1.ffi count ms = (res, post, s2.ffi) :=
  riscv limit s1 s2 res mc code labs asm ms pc target layout.1
    (LabBound.static_of_stateRel mc code labs pc s1 asm ms related layout.2)
    oracles execution success related

end InitECandidate.Solver.LabBoundTight
#print axioms InitECandidate.Solver.LabBoundTight.riscv_static_target
