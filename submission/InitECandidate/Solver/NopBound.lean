import InitECandidate.Solver.EncoderClock
import InitECandidate.Solver.SkipCost

/-! A quantitative interface reusable by generic compiler simulations. -/
namespace InitECandidate.Solver.NopBound
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.Semantics.TargetProps

def Contract {width : Nat} [NeZero width] {S Q : Type}
    (target : HolAsmTarget width S Q) (bound : Nat) : Prop :=
  ∀ s1 s2 ms, asmStep target.config s1 (.inst .skip) s2 → targetStateRel target s1 ms →
    ∃ n, n + 1 ≤ bound ∧ EncoderClock.EncoderAt target s1 s2 ms (.inst .skip) n

theorem step {width : Nat} [NeZero width] {S Q σ : Type}
    (c : MachineConfig width S Q) (bound : Nat) (bounded : Contract c.target bound)
    (s1 : AsmState width) (ms1 : S) (io : HolFfiState σ)
    (h : encoderCorrect c.target ∧ c.progAddresses = s1.memDomain ∧
      ffiEntryPcsDisjoint c s1 (c.target.config.encode (.inst .skip)).length ∧
      interferenceOk c.nextInterfer (c.target.proj s1.memDomain) ∧
      asmStep c.target.config s1 (.inst .skip)
        (asmUpd (.inst .skip) (s1.pc + BitVec.ofNat width (c.target.config.encode (.inst .skip)).length) s1) ∧
      targetStateRel c.target s1 ms1) :
    ∃ l ms2, l ≤ bound ∧ ∀ k,
      evaluateTargetHOL c io (k + l) ms1 = evaluateTargetHOL (shiftInterfer l c) io k ms2 ∧
      findNextInterference c io (k + l) ms1 = findNextInterference (shiftInterfer l c) io k ms2 ∧
      targetStateRel c.target
        (asmUpd (.inst .skip) (s1.pc + BitVec.ofNat width (c.target.config.encode (.inst .skip)).length) s1) ms2 ∧
      l ≠ 0 := by
  obtain ⟨correct, domain, disjoint, interference, source, related⟩ := h
  obtain ⟨n, small, assertions⟩ := bounded s1 _ ms1 source related
  have nonempty := encOkNotEmpty c.target.config (.inst .skip) ⟨correct.1.1, source.2.2.2.2.2.2⟩
  obtain ⟨post, run⟩ := EncoderClock.evaluator_exact c s1 _ ms1 io (.inst .skip) n correct.1
    domain disjoint interference source related assertions nonempty
  exact ⟨n + 1, post, small, run⟩

/-- RISC-V NOP has one actual evaluator/native transition, with the full
interference and memory assertion contract retained. -/
theorem riscv_one : Contract Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget 1 := by
  intro source post machine step related
  exact ⟨0, by decide, SkipCost.skip_encoder_exact source post machine ⟨step, related⟩⟩

/-- Padding NOPs cost one step and occupy at least four bytes. -/
def PaddingContract {width : Nat} [NeZero width] {S Q : Type}
    (target : HolAsmTarget width S Q) : Prop :=
  Contract target 1 ∧ 4 ≤ (target.config.encode (.inst .skip)).length

theorem riscv_padding : PaddingContract Flapjack.Compiler.Encoders.RiscV.Target.riscvTarget :=
  ⟨riscv_one, by decide⟩

end InitECandidate.Solver.NopBound

#print axioms InitECandidate.Solver.NopBound.step
#print axioms InitECandidate.Solver.NopBound.riscv_one

#print axioms InitECandidate.Solver.NopBound.riscv_padding
