import InitECandidate.Solver.EncoderClock

/-! A quantitative interface reusable by generic compiler simulations. -/
namespace InitECandidate.Solver.EncoderBound
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.Semantics.TargetProps

def Contract {width : Nat} [NeZero width] {S Q : Type}
    (target : HolAsmTarget width S Q) (bound : Nat) : Prop :=
  ∀ s1 i s2 ms, asmStep target.config s1 i s2 → targetStateRel target s1 ms →
    ∃ n, n + 1 ≤ bound ∧ EncoderClock.EncoderAt target s1 s2 ms i n

theorem step {width : Nat} [NeZero width] {S Q σ : Type}
    (c : MachineConfig width S Q) (bound : Nat) (bounded : Contract c.target bound)
    (s1 : AsmState width) (ms1 : S) (io : HolFfiState σ) (i : HolAsm width)
    (h : encoderCorrect c.target ∧ c.progAddresses = s1.memDomain ∧
      ffiEntryPcsDisjoint c s1 (c.target.config.encode i).length ∧
      interferenceOk c.nextInterfer (c.target.proj s1.memDomain) ∧
      asmStep c.target.config s1 i
        (asmUpd i (s1.pc + BitVec.ofNat width (c.target.config.encode i).length) s1) ∧
      targetStateRel c.target s1 ms1) :
    ∃ l ms2, l ≤ bound ∧ ∀ k,
      evaluateTargetHOL c io (k + l) ms1 = evaluateTargetHOL (shiftInterfer l c) io k ms2 ∧
      findNextInterference c io (k + l) ms1 = findNextInterference (shiftInterfer l c) io k ms2 ∧
      targetStateRel c.target
        (asmUpd i (s1.pc + BitVec.ofNat width (c.target.config.encode i).length) s1) ms2 ∧
      l ≠ 0 := by
  obtain ⟨correct, domain, disjoint, interference, source, related⟩ := h
  obtain ⟨n, small, assertions⟩ := bounded s1 i _ ms1 source related
  have nonempty := encOkNotEmpty c.target.config i ⟨correct.1.1, source.2.2.2.2.2.2⟩
  obtain ⟨post, run⟩ := EncoderClock.evaluator_exact c s1 _ ms1 io i n correct.1
    domain disjoint interference source related assertions nonempty
  exact ⟨n + 1, post, small, run⟩

end InitECandidate.Solver.EncoderBound

#print axioms InitECandidate.Solver.EncoderBound.step
