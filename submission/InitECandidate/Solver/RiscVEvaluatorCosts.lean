import InitECandidate.Solver.EncoderClock
import InitECandidate.Solver.SkipCost
import InitECandidate.Solver.MemoryCost
import InitECandidate.Solver.LocCost
import Flapjack.RiscV.CorrectnessEncoding.Length

/-! Exact costs in the actual evaluator for three complete ASM constructors.
The premises are the original assembly step/relation and evaluator guards.
No successful target execution or unknown clock offset is a premise. -/
namespace InitECandidate.Solver.RiscVEvaluatorCosts
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps
open InitECandidate.Solver.EncoderClock

/-- Observable evaluator prefix, with its exact cost and final ASM relation. -/
def Prefix {σ : Type} (mc : MachineConfig 64 riscv_state RiscVProjection)
    (io : HolFfiState σ) (ms : riscv_state) (s2 : AsmState 64) (cost : Nat) : Prop :=
  ∃ post,
    (∀ clock, evaluateTargetHOL mc io (clock + cost) ms =
      evaluateTargetHOL (shiftInterfer cost mc) io clock post) ∧
    targetStateRel riscvTarget s2 post

/-- Specialize the generic bridge without importing the full compiler proof. -/
theorem from_encoder {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (io : HolFfiState σ) (s1 s2 : AsmState 64) (ms : riscv_state)
    (i : HolAsm 64) (n : Nat)
    (target : mc.target = riscvTarget)
    (domain : mc.progAddresses = s1.memDomain)
    (disjoint : ffiEntryPcsDisjoint mc s1 (riscvEnc i).length)
    (interference : interferenceOk mc.nextInterfer (riscvTarget.proj s1.memDomain))
    (step : asmStep riscvConfig s1 i s2)
    (related : targetStateRel riscvTarget s1 ms)
    (cost : EncoderAt riscvTarget s1 s2 ms i n) :
    Prefix mc io ms s2 (n + 1) := by
  have ok : targetOk mc.target := by
    rw [target]
    exact Flapjack.RiscV.TargetProof.riscv_target_ok
  have encode : mc.target.config.encode i = riscvEnc i := by rw [target]; rfl
  obtain ⟨post, run⟩ := evaluator_exact mc s1 s2 ms io i n ok domain
    (by simpa only [encode] using disjoint)
    (by simpa only [target] using interference)
    (by simpa only [target, riscvTarget, riscvConfig_encode] using step)
    (by simpa only [target] using related)
    (by simpa only [target] using cost)
    (by rw [encode]; exact (Flapjack.RiscV.TargetProof.riscv_encoding i).2)
  exact ⟨post, fun clock => (run clock).1, by simpa only [target] using (run 0).2.2.1⟩

theorem skip_one {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (io : HolFfiState σ) (s1 s2 : AsmState 64) (ms : riscv_state)
    (target : mc.target = riscvTarget)
    (domain : mc.progAddresses = s1.memDomain)
    (disjoint : ffiEntryPcsDisjoint mc s1 (riscvEnc (.inst .skip)).length)
    (interference : interferenceOk mc.nextInterfer (riscvTarget.proj s1.memDomain))
    (step : asmStep riscvConfig s1 (.inst .skip) s2)
    (related : targetStateRel riscvTarget s1 ms) : Prefix mc io ms s2 1 :=
  from_encoder mc io s1 s2 ms _ 0 target domain disjoint interference step related
    (SkipCost.skip_encoder_exact s1 s2 ms ⟨step, related⟩)

theorem memory_one {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (io : HolFfiState σ) (s1 s2 : AsmState 64) (ms : riscv_state)
    (m : HolMemop) (r base : Nat) (w : BitVec 64)
    (target : mc.target = riscvTarget)
    (domain : mc.progAddresses = s1.memDomain)
    (disjoint : ffiEntryPcsDisjoint mc s1 (riscvEnc (.inst (.mem m r (.addr base w)))).length)
    (interference : interferenceOk mc.nextInterfer (riscvTarget.proj s1.memDomain))
    (step : asmStep riscvConfig s1 (.inst (.mem m r (.addr base w))) s2)
    (related : targetStateRel riscvTarget s1 ms) : Prefix mc io ms s2 1 :=
  from_encoder mc io s1 s2 ms _ 0 target domain disjoint interference step related
    (MemoryCost.memory_encoder_exact m r base w s1 s2 ms ⟨step, related⟩)

theorem loc_two {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (io : HolFfiState σ) (s1 s2 : AsmState 64) (ms : riscv_state)
    (r : Nat) (offset : BitVec 64)
    (target : mc.target = riscvTarget)
    (domain : mc.progAddresses = s1.memDomain)
    (disjoint : ffiEntryPcsDisjoint mc s1 (riscvEnc (.loc r offset)).length)
    (interference : interferenceOk mc.nextInterfer (riscvTarget.proj s1.memDomain))
    (step : asmStep riscvConfig s1 (.loc r offset) s2)
    (related : targetStateRel riscvTarget s1 ms) : Prefix mc io ms s2 2 :=
  from_encoder mc io s1 s2 ms _ 1 target domain disjoint interference step related
    (LocCost.loc_encoder_exact r offset s1 s2 ms ⟨step, related⟩)

end InitECandidate.Solver.RiscVEvaluatorCosts

#print axioms InitECandidate.Solver.RiscVEvaluatorCosts.from_encoder
#print axioms InitECandidate.Solver.RiscVEvaluatorCosts.skip_one
#print axioms InitECandidate.Solver.RiscVEvaluatorCosts.memory_one
#print axioms InitECandidate.Solver.RiscVEvaluatorCosts.loc_two
